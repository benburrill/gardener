#!/usr/bin/env python3
"""
A symlink farm manager akin to GNU Stow, but with additional features
that are useful for tasks such as managing dotfiles.
"""

__version__ = "0.3.0"


import os
import sys
import pathlib
import shutil
import time
import json
import enum
import functools
import collections
import inspect
import argparse


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
    try:
        actions = list(gen)
    except Exception as e:
        exit_with_error(str(e))

    if not actions:
        print("Nothing would be done")
    else:
        print("The following actions would be performed:")
        for action in actions:
            print(bullet(describe_action(action)))


def run(gen, *, verbose=False):
    try:
        actions = list(gen)
    except Exception as e:
        exit_with_error(str(e))

    remaining = iter(actions)

    if verbose and not actions:
        print("Nothing to do")

    try:
        for action in remaining:
            if verbose:
                print(describe_action(action), end=" ... ")

            action()

            if verbose:
                print("done")
    except Exception:
        if verbose:
            print("failed!")

        print(
            f"Action failed: {describe_action(action)}",
            file=sys.stderr
        )

        remaining = list(remaining)
        if remaining:
            print(
                "Additionally, the following subsequent actions could "
                "not performed:",
                file=sys.stderr
            )

            for action in remaining:
                print(describe_action(action), file=sys.stderr)

        print(
            "Encountered an exception while running planned actions.  "
            "Errors are supposed to be caught in the planning stage, "
            "so this likely indicates a bug in gardener!",
            file=sys.stderr
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


def add_custom_help(parser, help="Show this help message and exit."):
    # Although argparse adds -h and --help by default, the help says
    # "show this help message and exit" in lowercase.
    # I prefer it capitalized with a period at the end, so I do not use
    # this default behavior.
    parser.add_argument(
        "-h", "--help", action="help",
        default=argparse.SUPPRESS, help=help
    )

    return parser


common_opts = argparse.ArgumentParser(add_help=False)
common_opts.add_argument(
    "--weeds", metavar="<strategy>", dest="weed_strat",
    type=WeedStrategy, default="fail",
    help="The weed conflict resolution strategy to use.  "
         "When 'fail' is used, conflicts result in an "
         "error, with 'compost', conflicting weeds are "
         "backed up, and with 'herbicide', conflicting "
         "weeds are deleted.  [default: %(default)s]"
)

common_opts.add_argument(
    "--no-shadow", action="store_true",
    help="When two packages provide the same file, produce an error."
)

common_opts.add_argument(
    "--shadow", dest="no_shadow", action="store_false",
    help="When two packages provide the same file, the file from the "
         "lower precedence package is silently shadowed.  "
         "[This is the default behavior]"
)
common_opts.set_defaults(no_shadow=False)

common_opts.add_argument(
    "--dry", dest="runner",
    action="store_const", const=dry_run, default=run,
    help="Perform a dry run.  Actions are printed, but not executed."
)
common_opts.add_argument(
    "--verbose", action="store_true",
    help="Show the actions performed by gardener during execution.  "
         "This has no effect in a dry run."
)

cmd_gardener = add_custom_help(argparse.ArgumentParser(
    description="""
    Gardener is a symlink farm manager akin to GNU Stow, but with
    additional features that are useful for tasks such as managing
    dotfiles.
    """, add_help=False
))
cmd_gardener.add_argument(
    "--version", action="version",
    version=f"Symlink Gardener, version {__version__}",
    help="Show the version number and exit."
)
cmd_gardener.add_argument(
    "-g", "--garden", default=".", metavar="<garden>",
    help="Directory of the garden.  If no garden exists, gardener will "
         "search parent directories.  [default: %(default)s]"
)

subparsers = cmd_gardener.add_subparsers(
    dest="invoked_subcommand", metavar="<subcommand>"
)


def exit_with_error(message, status=2):
    # Similar to cmd_gardener.error, but doesn't print usage summary
    cmd_gardener.exit(
        message=f"{cmd_gardener.prog}: error: {message}\n",
        status=status
    )

def find_garden(args):
    garden_root = abspath(pathlib.Path(args.garden))

    while True:
        garden = Garden(garden_root)

        if garden.shed_path.is_dir():
            return garden

        if garden_root.parents:
            garden_root = garden_root.parent
        else:
            exit_with_error(
                f"Could not find a garden at {args.garden}\n"
                "Use ``gardener prepare`` to create a new garden."
            )

def get_tend_args(args):
    return dict(weed_strat=args.weed_strat, no_shadow=args.no_shadow)


# TODO: I'd like to preserve newlines without removing wrapping in
# descriptions.  I did try to write the messages to be readable without
# newlines, and I think they're ok, but I'd still prefer newlines.

cmd_prepare = argparse.ArgumentParser(add_help=False)
cmd_prepare.add_argument(
    "--reset", action="store_true",
    help="If passed, any existing garden will be cleared."
)
cmd_prepare = add_custom_help(subparsers.add_parser(
    "prepare", help="Create a garden.",
    description="""
    Create a garden in the current working directory (or the directory
    specified by --garden passed directly to the gardener command).
    """, add_help=False,
    parents=[cmd_prepare, common_opts]
))
def task_prepare(args):
    # We do not use find_garden here, since there is no garden to find.
    return Garden(pathlib.Path(args.garden)).prepare(
        reset=args.reset, **get_tend_args(args)
    )
cmd_prepare.set_defaults(task=task_prepare)


cmd_tend = add_custom_help(subparsers.add_parser(
    "tend", help="Update links.",
    description="""
    Update links.

    Old links will be deleted and new ones created in response to
    changes in the installed packages.
    """, add_help=False,
    parents=[common_opts]
))
def task_tend(args):
    return find_garden(args).tend(**get_tend_args(args))
cmd_tend.set_defaults(task=task_tend)


cmd_plant = argparse.ArgumentParser(add_help=False)
cmd_plant.add_argument(
    "--replace", action="store_true",
    help="Replace any existing package with the same name."
)
cmd_plant = add_custom_help(subparsers.add_parser(
    "plant", help="Install package(s) to the garden.",
    description="Install package(s) to the garden.", add_help=False,
    parents=[cmd_plant, common_opts]
))
cmd_plant.add_argument(
    "packages", nargs="*", type=parse_package, metavar="[name:]path",
    help="""
    The path to a package directory to install, or a name:path pair.
    If a name is not provided, the package directory name is used as the
    package name.
    """
)
def task_plant(args):
    new = collections.OrderedDict(args.packages)
    return find_garden(args).plant(
        new, replace=args.replace, **get_tend_args(args)
    )
cmd_plant.set_defaults(task=task_plant)


cmd_prune = add_custom_help(subparsers.add_parser(
    "prune", help="Uninstall package(s) from the garden.",
    description="""
    Uninstall package(s) from the garden.

    The symlinks of the packages specified by their package names are
    removed from the garden.

    The package directory itself is not deleted.
    """, add_help=False,
    parents=[common_opts]
))
cmd_prune.add_argument(
    "package_names", nargs="*", metavar="<package-names>",
    help="Packages to uninstall (to list installed packages, run "
         "gardener list)."
)
def task_prune(args):
    return find_garden(args).prune(
        args.package_names, **get_tend_args(args)
    )
cmd_prune.set_defaults(task=task_prune)


cmd_cultivate = argparse.ArgumentParser(add_help=False)
cmd_cultivate.add_argument(
    "-p", "--package", required=True, metavar="<package-name>",
    help="The target package. [required]"
)
cmd_cultivate = add_custom_help(subparsers.add_parser(
    "cultivate", help="Add weed(s) to a package.",
    description="""
    Add weed(s) to a package.

    The files are moved to the package specified by a package name, and
    are symlinked back into the garden.
    """, add_help=False,
    parents=[cmd_cultivate, common_opts]
))
cmd_cultivate.add_argument(
    "files", nargs="*", type=pathlib.Path, metavar="<files>",
    help="Paths to weed files to add to the package."
)
def task_cultivate(args):
    return find_garden(args).cultivate(
        args.package, args.files, **get_tend_args(args)
    )
cmd_cultivate.set_defaults(task=task_cultivate)


cmd_fallow = add_custom_help(subparsers.add_parser(
    "fallow", help="Move file(s) out from their package.",
    description="""
    Move file(s) out from their package.

    The garden symlinks referred to by the specified files are replaced
    with the file itself, turning them into weeds.

    In other words, this command reverses the effects of cultivate.
    """, add_help=False,
    parents=[common_opts]
))
cmd_fallow.add_argument(
    "files", nargs="*", type=pathlib.Path, metavar="<files>",
    help="Paths to files to convert into weeds."
)
def task_fallow(args):
    return find_garden(args).fallow(
        args.files, **get_tend_args(args)
    )
cmd_fallow.set_defaults(task=task_fallow)


cmd_arrange = argparse.ArgumentParser(add_help=False)
front_back = cmd_arrange.add_mutually_exclusive_group(required=True)
front_back.add_argument(
    "--front", dest="front", action="store_true",
    help="Give the package the highest precedence."
)
front_back.add_argument(
    "--back", dest="front", action="store_false",
    help="Give the package the lowest precedence."
)
front_back.set_defaults(front=None)

cmd_arrange = add_custom_help(subparsers.add_parser(
    "arrange", help="Change the precedence of a package.",
    description="""
    Change the precedence of a package.

    This affects the shadowing of files.
    """, add_help=False,
    # custom usage string to emphasize --front and --back
    usage="%(prog)s [options] <package-name> (--front | --back)",
    parents=[cmd_arrange, common_opts]
))
cmd_arrange.add_argument(
    "package_name", metavar="<package-name>",
    help="The target package."
)
def task_arrange(args):
    return find_garden(args).arrange(
        args.package_name, front=args.front, **get_tend_args(args)
    )
cmd_arrange.set_defaults(task=task_arrange)


cmd_list = add_custom_help(subparsers.add_parser(
    "list", help="List installed packages.",
    description="List installed packages.",
    aliases=["packages"],  # alias for original command name
    add_help=False
))
def task_list(args):
    for name in find_garden(args).manifest:
        print(name)
cmd_list.set_defaults(task=task_list)


cmd_help = add_custom_help(subparsers.add_parser(
    "help", help="Display help about a subcommand.",
    description="""
    Display help about a subcommand.

    If <subcommand> is not passed, general help about gardener is shown
    instead.
    """, add_help=False
), help=argparse.SUPPRESS)
cmd_help.add_argument(
    "subcommand", nargs="?", metavar="<subcommand>",
    choices=list(subparsers.choices),
    help=f"List of commands: {', '.join(map(repr, subparsers.choices))}"
)
def task_help(args):
    if args.subcommand is None:
        cmd_gardener.print_help()
    else:
        subparsers.choices[args.subcommand].print_help()
cmd_help.set_defaults(task=task_help)


def main(*args, **kwargs):
    args = cmd_gardener.parse_args(*args, **kwargs)
    if args.invoked_subcommand is None:
        cmd_gardener.print_help(file=sys.stderr)
        cmd_gardener.exit(2)
    else:
        try:
            result = args.task(args)
        except Exception as e:
            exit_with_error(str(e))
        if hasattr(args, "runner"):
            assert result is not None
            args.runner(result, verbose=args.verbose)


if __name__ == "__main__":
    main()
