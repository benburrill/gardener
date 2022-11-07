import codecs
import os
import re

from setuptools import setup


# read and find_version from pip/setup.py {{{
here = os.path.abspath(os.path.dirname(__file__))


def read(*parts):
    # intentionally *not* adding an encoding option to open, See:
    #   https://github.com/pypa/virtualenv/issues/201#issuecomment-3145690
    with codecs.open(os.path.join(here, *parts), 'r') as fp:
        return fp.read()


def find_version(*file_paths):
    version_file = read(*file_paths)
    version_match = re.search(r"^__version__ = ['\"]([^'\"]*)['\"]",
                              version_file, re.M)
    if version_match:
        return version_match.group(1)
    raise RuntimeError("Unable to find version string.")
# }}}


setup(
    name="symlink-gardener",
    version=find_version("gardener.py"),
    description="A symlink farm manager akin to GNU Stow",
    long_description=read("README.rst"),
    author="Ben Burrill",
    author_email="bburrill98+symlink-gardener@gmail.com",
    url="https://github.com/benburrill/gardener",
    py_modules=["gardener"],
    entry_points={
        "console_scripts": [
            "gardener = gardener:main"
        ]
    },
    install_requires=[
        "click >= 8"
    ],
    license="MIT",
    classifiers=["Programming Language :: Python :: 3",
                 "Programming Language :: Python :: 3 :: Only",
                 "License :: OSI Approved :: MIT License",
                 "Topic :: System :: Archiving :: Packaging",
                 "Topic :: System :: Filesystems",
                 "Topic :: Utilities"]
)

# vim: foldmethod=marker
