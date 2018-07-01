Symlink Gardener
================

Symlink Gardener is a symlink farm manager akin to GNU Stow, but with
additional features that are useful for tasks such as managing dotfiles.

Features
--------

- Options for conflict resolution.  By default, packages will silently
  shadow symlinks from packages with lower precedence than them, but
  actions will fail when there are conflicts with "weeds" (files not
  owned by the garden).  However, different conflict resolution
  strategies can also be specified.
- A more tangible concept of packages than stow.  Packages can have
  their own config files to declare files to ignore (and maybe more
  stuff in the future), and packages have a real concept of being
  installed which allows symlinks to be easily and accurately updated
  when packages change.
- Commands for converting specific weeds into symlinks managed by the
  garden and vice-versa.
- And most importantly -- hastily tacked on gardening metaphors!

Installation
------------

Python >= 3.6 is required.

Recommended installation (with `pipsi`_):

.. code:: shell

    $ pipsi install --python=python3 symlink-gardener

Basic Usage
-----------

Create a garden in the current directory

.. code:: shell

    $ gardener prepare

Plant (install) packages in the garden

This creates symlinks in the garden directory at paths that correspond
to those in the package directory.

Packages may be customized in ``/.garden-package.json`` (currently all
you can do is add ignore patterns)

.. code:: shell

    $ gardener plant path/to/common path/to/ex other-ex:path/to/other/ex

Update symlinks for all installed packages

.. code:: shell

    $ gardener tend

Add weeds to an installed package.

This moves the specified files from the garden directory to the package
and creates a symlink in their place.

.. code:: shell

    $ gardener cultivate -p common some/file another/file

Turn those symlinks back into weeds.

.. code:: shell

    $ gardener fallow some/file another/file


Change package precedence.

This causes symlinks owned by ex to shadow symlinks owned by all other
packages.  Earlier, the package other-ex was in front of it.

.. code:: shell

    $ gardener arrange --front ex

Prune (uninstall) packages

.. code:: shell

    $ gardener prune ex other-ex

See the help for more

.. code:: shell

    $ gardener help

.. .. .. .. .. .. .. .. .. .. .. .. .. .. .. .. .. .. .. .. .. .. .. ..
.. Links
.. _pipsi: https://github.com/mitsuhiko/pipsi
