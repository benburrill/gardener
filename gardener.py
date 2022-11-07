"""
A symlink farm manager akin to GNU Stow, but with additional features
that are useful for tasks such as managing dotfiles.
"""

__version__ = "0.2.4"


import os
import pathlib
import shutil
import time
import json
import enum
import functools
import collections
import inspect
import click


# This is the name of the shed directory that indicates the presence of
# a garden.
SHED_NAME = ".symlink-garden"


def file_tree(root, *, rel=None):
    """
    Recursively walks the ``root`` directory, yielding only files (no
    directories) as relative paths to ``rel``.  If ``rel`` is None,
    the paths are relative to ``root``.
    """
    
    rel = root if rel is None else rel

    for path in root.iterdir():
        if path.is_dir():
            yield from file_tree(path, rel=rel)
        else:
            yield path.relative_to(rel)


def readlink(path):
    """
    kinda like resolve, but returns the literal path pointed to by a
    symlink rather than resolving it further
    """
    return pathlib.Path(os.readlink(path))

def abspath(path):
    """
    kinda like resolve, but doesn't follow symlinks
    """
    return pathlib.Path(os.path.abspath(path))


def move_adjust(from_path, to_path):
    """
    Move from_path to to_path, but adjust any relative symlinks so they
    don't break.  I don't know why shutil.move doesn't already do this.
    Hopefully there isn't a reason.
    """

    try:
        symlink_target = readlink(from_path)
    except OSError:
        symlink_target = None

    if symlink_target is None or symlink_target.is_absolute():
        shutil.move(from_path, to_path)
    else:
        # os.path.relpath is used rather than relative_to because it
        # uses ../ paths when needed.
        to_path.symlink_to(os.path.relpath(
            abspath(from_path.parent / symlink_target),
            to_path.parent
        ))

        from_path.unlink()


def deferred(func):
    @functools.wraps(func)
    def wrapped(*args, **kwargs):
        return functools.partial(func, *args, **kwargs)
    return wrapped


def describe_action(action):
    doc = action.func.__doc__ or action.func.__name__
    return doc.format(**inspect.getcallargs(
        action.func, *action.args, **action.keywords
    ))


class PackageOwnershipError(OSError):
    pass


class FileIsNotAWeedError(PackageOwnershipError):
    pass


class FileIsAWeedError(PackageOwnershipError, FileExistsError):
    pass


class Package:
    def __init__(self, name, root):
        self.name = name
        self.root = abspath(root)
        self.config = collections.ChainMap(
            self.read_config(),
            self.default_config
        )

    @classmethod
    def from_path(cls, path):
        return cls(path.name, path)
    
    default_config = {
        # TODO: it might be nice to have saner defaults.  For example,
        # we could ignore clutter files (like .DS_Store on OSX and
        # desktop.ini on Windows) by default, and maybe even things like
        # README files too.
        # Currently though, since I use ChainMap to deal with defaults,
        # any non-trivial defaults are a bad idea.  Also, since I have
        # no way to have explicit includes yet, there would be no way to
        # unignore these defaults.
        "ignore": []
    }

    def read_config(self):
        if not self.config_path.exists():
            return {}

        with self.config_path.open() as cfile:
            return json.load(cfile)

    @property
    def config_path(self):
        preferred = self.root / "GARDEN_PACKAGE.json"
        if preferred.exists():
            return preferred

        # Backwards compatibility with old name for this.  I changed it
        # because it looked weird for a package configuration file,
        # especially when used with dotfiles.
        return self.root / ".garden-package.json"

    @property
    def paths(self):
        return {path for path in file_tree(self.root)
                if not self.is_ignored(path)}

    def is_ignored(self, path):
        """
        ``path`` is a relative path to the root of the package.
        """
        # TODO: I would like better syntax for ignores, including a way
        # to specify whether the match is recursive as well support for
        # explicit inclusions that override ignores.
        return (path == self.config_path.relative_to(self.root)
                or pathlib.Path(SHED_NAME) in path.parents
                or any(path.match(ig) for ig in self.config["ignore"]))
    
    def owns(self, abs_path):
        """
        Returns True if the path is a symlink pointing to somewhere in
        the package.

        The ``owns`` method disregards whether the file is ignored or
        even exists in the package.
        """
        
        try:
            to = readlink(abs_path)
        except OSError:
            return False

        return self.root in abspath(to).parents


PackageRecord = collections.namedtuple(
    "PackageRecord", ["package", "paths"]
)


class WeedStrategy(enum.Enum):
    FAIL = "fail"
    COMPOST = "compost"
    HERBICIDE = "herbicide"


class Garden:
    def __init__(self, root):
        if not root.is_dir():
            raise NotADirectoryError(
                f"{abspath(root)} is not a directory and cannot be "
                f"used as the garden root."
            )

        self.root = abspath(root)
        self.manifest = self.read_manifest()
        self.dead = set()
        self.dirty = False

    @property
    def shed_path(self):
        return self.root / SHED_NAME

    @property
    def manifest_path(self):
        return self.shed_path / "manifest.json"

    def read_manifest(self):
        if not self.manifest_path.exists():
            return collections.OrderedDict()

        with self.manifest_path.open() as mfile:
            manifest = json.load(
                mfile, object_pairs_hook=collections.OrderedDict
            )

        for name, record in manifest.items():
            manifest[name] = PackageRecord(
                Package(name, pathlib.Path(record["root"])),
                {pathlib.Path(path) for path in record["paths"]}
            )
        
        return manifest

    def owns(self, abs_path):
        """
        Returns True if ``abs_path`` is not a weed (i.e. either nothing
        exists at the path or it is a symlink owned by an installed
        package).
        """

        try:
            rel_path = abs_path.relative_to(self.root)
        except ValueError:
            return False

        return (
            not os.path.lexists(abs_path)
            or any(rec.package.owns(abs_path)
                   for rec in self.manifest.values())
            or any(dead_package.owns(abs_path)
                   for dead_package in self.dead)
        )

    def owner(self, rel_path):
        """
        Returns the owner package for a path, or None if the path refers
        to a weed or empty soil.
        """

        return next((
            rec.package for rec in reversed(self.manifest.values())
            if rel_path in rec.package.paths
        ), None)

    def new_compost_bin(self):
        """
        A "compost bin" is a package to throw weeds into in case of
        conflicts.
        """

        # TODO: prettier timestamp maybe
        name = f"weeds-{time.time()}"
        return Package.from_path(
            self.shed_path / "weeds" / name
        )

    def resolve_weed_conflict(self, weed_strat, path, compost_bin):
        if weed_strat == WeedStrategy.FAIL:
            raise FileIsAWeedError(
                f"Weed conflict at {self.root / path} -- file already "
                f"exists, but is not owned by the garden."
            )
        elif weed_strat == WeedStrategy.COMPOST:
            yield self.do_move_to_package(compost_bin, path)
        elif weed_strat == WeedStrategy.HERBICIDE:
            yield self.do_delete_weed(path)
        else:
            raise RuntimeError(
                f"Bad conflict resolution strategy {weed_strat}."
            )

    def tend(self, *, weed_strat=WeedStrategy.FAIL, no_shadow=False):
        compost_bin = self.new_compost_bin()
        disowned = {}
        links = {}

        # Wrap with list because we may mutate self.manifest
        for rec in list(self.manifest.values()):
            if not rec.package.root.is_dir():
                yield from self.prune([rec.package.name], _tend=False)
                continue

            good = rec.package.paths
            bad = rec.paths - good
            
            for path in good:
                if no_shadow and path in links:
                    raise PackageOwnershipError(
                        f"Symlink to {rec.package.root / path} would "
                        f"shadow symlink to {links[path].root / path}."
                    )
                
                if path in links:
                    disowned.setdefault(links[path], set()).add(path)

                links[path] = rec.package
            
            for path in bad:
                rec.paths.remove(path)
                self.dirty = True

                if rec.package.owns(self.root / path):
                    yield self.do_prune_symlink(rec.package, path)

        for path, package in links.items():
            abs_path = self.root / path
            if not self.owns(abs_path):
                yield from self.resolve_weed_conflict(
                    weed_strat, path, compost_bin
                )

            known = self.manifest[package.name].paths
            
            # Only dirty if we don't know about it already
            if path not in known:
                known.add(path)
                self.dirty = True

            if not package.owns(abs_path):
                yield self.do_write_symlink(package, path, no_shadow)
        
        for package, bad_paths in disowned.items():
            known_paths = self.manifest[package.name].paths
            if not known_paths.isdisjoint(bad_paths):
                known_paths.difference_update(bad_paths)
                self.dirty = True
        
        yield from self.clean()

    def prepare(self, *, reset=False, **tend_args):
        if reset:
            yield from self.prune(list(self.manifest), **tend_args)
        elif self.shed_path.exists():
            raise FileExistsError(
                f"Garden already exists at {self.root}"
            )

        self.dirty = True
        yield from self.clean()

    def plant(self, new, *, replace=False, **tend_args):
        for name, package in new.items():
            if not package.root.is_dir():
                raise NotADirectoryError(
                    f"{package.root} is not a directory and cannot be "
                    f"used as a package root."
                )

            if not replace and name in self.manifest:
                raise ValueError(
                    f"A package named {name!r} is already planted in "
                    f"{self.root}."
                )
            
            self.manifest[name] = PackageRecord(package, set())
            self.dirty = True

        yield from self.tend(**tend_args)
        yield from self.clean()
    
    def _walk_paths(self, garden_paths):
        # Takes a list of files and directories, yields both files and
        # sub-files, making them all relative to the garden.
        for garden_path in garden_paths:
            if garden_path.is_dir():
                yield from file_tree(
                    abspath(garden_path), rel=self.root
                )
            else:
                yield abspath(garden_path).relative_to(self.root)

    def cultivate(self, package_name, paths, **tend_args):
        # Make sure the packages are up-to-date before we do anything.
        # Note that we can't do a tend at the end of this function.
        # This is because the action of moving the file to the package
        # is deferred, so the package won't know it has the new files
        # until later.  From its perspective, the new file we add to the
        # manifest would have been deleted from the package.  This means
        # that we must be careful not to do something that tend wouldn't
        # here.  This makes things like the later test to see if the
        # garden already owns the file not only helpful to the user, but
        # necessary for correctness -- if non-weeds could be cultivated,
        # a re-tend would be needed to sort out shadowing.
        yield from self.tend(**tend_args)

        rec = self.manifest[package_name]
        package = rec.package

        for path in self._walk_paths(paths):
            garden_path = self.root / path
            target_path = rec.package.root / path
            owner = self.owner(path)

            if owner is rec.package:
                # Already cultivated
                continue
            
            if owner is not None:
                raise PackageOwnershipError(
                    f"The file at {path} is owned by another package: "
                    f"{owner.name!r}."
                )

            if os.path.lexists(target_path):
                raise FileExistsError(
                    f"The package {rec.package.name!r} already has a "
                    f"file at {path}."
                )

            yield self.do_move_to_package(rec.package, path)
            if not rec.package.is_ignored(path):
                rec.paths.add(path)
                self.dirty = True

                yield self.do_write_symlink(rec.package, path, True)
        
        yield from self.clean()
    
    def fallow(self, paths, **tend_args):
        # Like cultivate, this function needs to be careful about tend
        # It's important to remember that weed conflicts have already
        # been dealt with in self.tend, even if it doesn't look like it.
        yield from self.tend(**tend_args)

        for path in self._walk_paths(paths):
            garden_path = self.root / path

            # TODO: this is similar to ``owner``, maybe we should
            # actually have a ``owners`` method and have it yield
            # records rather than packages.
            recs = [rec for rec in self.manifest.values()
                    if path in rec.package.paths]
            
            if not recs:
                # Path is already fallow
                continue

            rec = recs.pop()

            if recs:
                raise PackageOwnershipError(
                    f"{garden_path} is provided by multiple packages, "
                    f"would result in weed conflict cascade.  Shadowed "
                    f"packages: {[rec.package.name for rec in recs]}"
                )
            
            rec.paths.remove(path)
            self.dirty = True

            yield self.do_move_out_of_package(rec.package, path)

        yield from self.clean()

    def prune(self, package_names, *, _tend=True, **tend_args):
        for package_name in package_names:
            rec = self.manifest.pop(package_name)
            self.dirty = True

            for path in rec.paths:
                if rec.package.owns(self.root / path):
                    yield self.do_prune_symlink(rec.package, path)

            self.dead.add(rec.package)
            yield self.do_finalize_package_prune(rec.package)

        yield from self.clean()

        if _tend:
            yield from self.tend(**tend_args)
    
    def arrange(self, package_name, *, front=True, **tend_args):
        old = list(self.manifest)
        self.manifest.move_to_end(package_name, last=front)
        if list(self.manifest) != old:
            self.dirty = True
        yield from self.clean()

        yield from self.tend(**tend_args)

    def clean(self):
        """
        Helper for do_write_manifest that writes to the manifest when
        needed, serializing it in the generator stage, and resetting the
        dirty flag.
        """

        if self.dirty:
            yield self.do_write_manifest(collections.OrderedDict(
                (name, {
                    "root": str(rec.package.root),
                    "paths": [str(path) for path in rec.paths]
                })
                for name, rec in self.manifest.items()
            ))

            self.dirty = False

    ### Deferred (or "action") functions ###############################
    # Operations that modify the filesystem are implemented as discrete
    # actions which are yielded by the primary interface methods.  This
    # allows dry runs to be performed, as well as making it easy to stop
    # an operation early if errors are detected.
    # 
    # Generally there shouldn't be errors in deferred functions unless
    # something went catastrophically wrong.  Errors should be found
    # early in the generators.  However, I will perform sanity checks
    # here that should be performed elsewhere (or indicate conditions
    # that shouldn't happen at all) and raise errors pointing these out
    # as bugs.
    # 
    # Deferred functions should also avoid touching the manifest and
    # other highly stateful objects, since they may change after the
    # deferred function is initially invoked, but before it actually
    # ends up getting called.  Instead, all the data they need should be
    # passed as parameters that are not expected to mutate.

    @deferred
    def do_delete_weed(self, path):
        "Delete weed at {self.root}/{path}"

        (self.root / path).unlink()

    @deferred
    def do_prune_symlink(self, package, path):
        "Prune symlink from package {package.name!r} at {self.root}/{path}"

        abs_path = self.root / path
        if not os.path.lexists(abs_path):
            # Nothing to do
            return

        if package.owns(abs_path):
            abs_path.unlink()
        else:
            raise PackageOwnershipError(
                f"{abs_path} is not owned by package {package.name!r} "
                f"and cannot be removed."
            )

    @deferred
    def do_move_to_package(self, package, path):
        "Move {self.root}/{path} to {package.root}/{path}"

        from_path = self.root / path
        to_path = package.root / path

        if os.path.lexists(to_path):
            raise FileExistsError(
                f"The package {package.name!r} already contains a file "
                f"at {path}."
            )

        to_path.parent.mkdir(parents=True, exist_ok=True)
        move_adjust(from_path, to_path)

    @deferred
    def do_move_out_of_package(self, package, path):
        "Move {package.root}/{path} to {self.root}/{path}"
        # TODO: maybe combine moving to/from packages?
        
        from_path = package.root / path
        to_path = self.root / path

        if os.path.lexists(to_path) and not package.owns(to_path):
            raise PackageOwnershipError(
                f"The package {package.name!r} does not own the file "
                f"at {to_path}."
            )

        to_path.parent.mkdir(parents=True, exist_ok=True)
        move_adjust(from_path, to_path)

    @deferred
    def do_write_symlink(self, package, path, no_shadow=False):
        "Write symlink {self.root}/{path} -> {package.root}/{path}"

        link_path = self.root / path
        target_path = package.root / path

        if target_path.is_dir():
            raise IsADirectoryError(
                f"{target_path} must be a file, not a directory."
            )

        # TODO: It's probably not a good idea to call self.owns() in a
        # deferred function, but I really don't care right now.
        if not self.owns(link_path):
            raise FileIsAWeedError(
                f"Unresolved weed conflict at {link_path}."
            )
        elif no_shadow and os.path.lexists(link_path):
            raise PackageOwnershipError(
                f"Symlink would shadow at {link_path}"
            )
        else:
            link_path.parent.mkdir(parents=True, exist_ok=True)

            if os.path.lexists(link_path):
                link_path.unlink()

            link_path.symlink_to(target_path)

    @deferred
    def do_write_manifest(self, serialized_manifest):
        "Commit changes to the garden's manifest"

        self.shed_path.mkdir(exist_ok=True)
        with self.manifest_path.open("w") as mfile:
            json.dump(serialized_manifest, mfile, indent=4)
    
    @deferred
    def do_finalize_package_prune(self, package):
        "Finalize prune of package {package.name!r}"
        self.dead.remove(package)


def bullet(string):
    return f" * {string}"


def dry_run(gen, **_):
    actions = list(gen)
    
    if not actions:
        click.echo("Nothing would be done")
    else:
        click.echo("The following actions would be performed:")
        for action in actions:
            click.echo(bullet(describe_action(action)))


def run(gen, *, verbose=False):
    actions = list(gen)
    remaining = iter(actions)

    if verbose and not actions:
        click.echo("Nothing to do")

    try:
        for action in remaining:
            if verbose:
                click.echo(f"{describe_action(action)} ... ", nl=False)

            action()

            if verbose:
                click.secho("done", fg="green")
    except Exception:
        if verbose:
            click.secho("failed!", fg="red")

        click.echo(
            click.style("Action failed: ", fg="yellow") +
            click.style(describe_action(action), fg="red"),
            err=True
        )

        remaining = list(remaining)
        if remaining:
            click.secho(
                "Additionally, the following subsequent actions could "
                "not performed:",
                fg="yellow", err=True
            )

            for action in remaining:
                click.secho(
                    bullet(describe_action(action)),
                    fg="red", err=True
                )
        
        click.secho(
            "Encountered an exception while running planned actions.  "
            "Errors are supposed to be caught in the planning stage, "
            "so this likely indicates a bug in gardener!",
            fg="yellow", err=True
        )

        # Traceback
        raise


def simple_run(gen):
    """
    This run function which never writes to stdout might be useful if
    gardener is used as a library for some reason.

    It is not used by the cli.
    """

    actions = list(gen)
    for action in actions:
        action()


def parse_package(package):
    *name, path = package.split(":", 1)
    path = pathlib.Path(path)
    if name:
        package = Package(*name, path)
    else:
        package = Package(path.name, path)
    return (package.name, package)


def common_opts(func):
    @click.option("--weeds", type=WeedStrategy, default="fail",
                  metavar="<strategy>", show_default=True,
                  help="The weed conflict resolution strategy to use.  "
                       "When 'fail' is used, conflicts result in an "
                       "error, with 'compost', conflicting weeds are "
                       "backed up, and with 'herbicide', conflicting "
                       "weeds are deleted.")
    @click.option("--shadow / --no-shadow", default=True,
                  help="If --no-shadow is passed, conflicts between "
                       "files of different packages causes an error.  "
                       "The default is to shadow files from packages "
                       "with lower precedence.")
    @click.option("--dry", is_flag=True,
                  help="Perform a dry run.  Actions are printed, but "
                       "not executed.")
    @click.option("--verbose", is_flag=True,
                  help="Show the actions performed by gardener during "
                       "execution.  This has no effect in a dry run.")
    @click.pass_context
    @functools.wraps(func)
    def wrapped(ctx, weeds, shadow, dry, verbose, **kwargs):
        ctx.obj["runner"] = dry_run if dry else run
        ctx.obj["verbose"] = verbose

        return func(
            ctx,
            weed_strat=weeds,
            no_shadow=not shadow,
            **kwargs
        )

    return wrapped


@click.group(options_metavar="[options]",
             subcommand_metavar="<command> [args]...")
@click.version_option(__version__, prog_name="Symlink Gardener")
@click.option("--garden", "-g", default=".",
              metavar="<path>", show_default=True,
              help="Directory of the garden.  If no garden exists, "
                   "gardener will search parent directories.")
@click.pass_context
def cli(ctx, garden):
    """
    Gardener is a symlink farm manager akin to GNU Stow, but with
    additional features that are useful for tasks such as managing
    dotfiles.
    """

    garden_root = abspath(pathlib.Path(garden))

    while True:
        garden = Garden(garden_root)

        if ctx.invoked_subcommand in {"prepare", "help"}:
            break

        if garden.shed_path.is_dir():
            break

        if garden_root.parents:
            garden_root = garden_root.parent
        else:
            raise FileNotFoundError(
                f"Could not find a garden.  Use ``gardener prepare`` "
                f"to create one."
            )

    ctx.obj["garden"] = garden

    # Should always be overridden by common_opts
    ctx.obj["runner"] = run
    ctx.obj["verbose"] = False


@cli.result_callback()
@click.pass_context
def do_it(ctx, gen, **_):
    if gen is not None:
        ctx.obj["runner"](gen, verbose=ctx.obj["verbose"])


@cli.command(options_metavar="[options]")
@click.argument("subcommand", required=False,
                metavar="[subcommand]")
@click.pass_context
def help(ctx, subcommand):
    """
    Display help about a subcommand.

    If [subcommand] is not passed, help about gardener is shown instead.
    """

    if subcommand is None:
        sctx = ctx.parent
    else:
        command = ctx.parent.command.commands[subcommand]
        sctx = click.Context(command, ctx.parent, subcommand)

    click.echo(sctx.get_help())


@cli.command(options_metavar="[options]")
@click.option("--reset", is_flag=True,
              help="If passed, any existing garden will be cleared.")
@common_opts
def prepare(ctx, reset, **tend_args):
    """
    Create a garden.

    Creates a garden in the directory specified by the --garden flag to
    gardener.
    """

    return ctx.obj["garden"].prepare(reset=reset, **tend_args)


@cli.command(options_metavar="[options]")
@common_opts
def tend(ctx, **tend_args):
    """
    Update links.

    Old links will be deleted and new ones created in response to
    changes in the installed packages.
    """

    return ctx.obj["garden"].tend(**tend_args)


@cli.command(options_metavar="[options]")
@click.option("--replace", is_flag=True,
              help="Replace any existing package with the same name.")
@click.argument("packages", nargs=-1, type=parse_package,
                metavar="[[name:]package-path]...")
@common_opts
def plant(ctx, packages, replace, **tend_args):
    """
    Install package(s) to the garden.

    The list of packages may take the form of paths to package
    directories or name:path pairs.  If a name is not provided for a
    package, the package directory name is used instead.
    """

    new = collections.OrderedDict(packages)
    return ctx.obj["garden"].plant(new, replace=replace, **tend_args)


@cli.command(options_metavar="[options] -p <package-name>")
@click.option("--package", "-p", required=True,
              metavar="<package-name>",
              help="The target package.")
@click.argument("files", nargs=-1, type=pathlib.Path,
                metavar="[files]...")
@common_opts
def cultivate(ctx, package, files, **tend_args):
    """
    Add weed(s) to a package.

    The files are moved to the package specified by a package name, and
    are symlinked back into the garden.
    """

    return ctx.obj["garden"].cultivate(package, files, **tend_args)


@cli.command(options_metavar="[options]")
@click.argument("files", nargs=-1, type=pathlib.Path,
                metavar="[files]...")
@common_opts
def fallow(ctx, files, **tend_args):
    """
    Move file(s) out from their package.

    The garden symlinks referred to by the specified files are replaced
    with the file itself, turning them into weeds.

    In other words, this command reverses the effects of cultivate.
    """

    return ctx.obj["garden"].fallow(files, **tend_args)


@cli.command(options_metavar="[options]")
@click.argument("package-names", nargs=-1,
                metavar="[package-names]...")
@common_opts
def prune(ctx, package_names, **tend_args):
    """
    Uninstall package(s) from the garden.

    The symlinks of the packages specified by their package names are
    removed from the garden.

    The package directory itself is not deleted.
    """

    return ctx.obj["garden"].prune(package_names, **tend_args)


@cli.command(options_metavar="[options] (--front|--back)")
@click.argument("package-name", metavar="package-name")
@click.option("--front / --back", default=None, required=True,
              help="Specifies how to arrange the package.")
@common_opts
def arrange(ctx, package_name, front, **tend_args):
    """
    Change the precedence of a package.

    \b
    --front gives the package the highest precedence
    --back gives the package the lowest precedence
    """

    return ctx.obj["garden"].arrange(package_name, front=front, **tend_args)


@cli.command(options_metavar="[options]")
@click.pass_context
def packages(ctx):
    """
    List installed packages.
    """

    for name in ctx.obj["garden"].manifest:
        click.echo(name)


def main():
    cli(obj={})


if __name__ == "__main__":
    main()
