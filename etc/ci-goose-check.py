#!/usr/bin/env python3

import shutil
import subprocess as sp
from dataclasses import dataclass


@dataclass
class Proj:
    name: str
    repo: str
    commit: str | None

    def path(self) -> str:
        return f"/tmp/{self.name}"

    @classmethod
    def make(cls, name, repo, commit=None):
        return cls(name, repo, commit)


projs = {
    "std": Proj.make(
        "std", "https://github.com/goose-lang/std", commit="upamanyus-fixes"
    ),
    "primitive": Proj.make(
        "primitive", "https://github.com/goose-lang/primitive", commit="upamanyus-fixes"
    ),
    "marshal": Proj.make(
        "marshal", "https://github.com/upamanyus/marshal", commit="upamanyus-fixes"
    ),
    "examples": Proj.make("examples", "https://github.com/mit-pdos/perennial-examples"),
    "etcd-raft": Proj.make(
        "etcd-raft", "https://github.com/upamanyus/etcd-raft", commit="goose"
    ),
    "etcd": Proj.make(
        "etcd",
        "https://github.com/upamanyus/etcd",
        commit="goose",
    ),
}


def checkout(proj: Proj):
    print(f"Checking out {proj.name}")
    path = proj.path()

    try:
        p = sp.run(
            ["git", "remote", "get-url", "origin"],
            text=True,
            capture_output=True,
            check=True,
            cwd=path,
        )
        assert p.stdout.strip() == proj.repo
        sp.run(["git", "reset", "--hard"], check=True, cwd=path)
        sp.run(["git", "pull"], check=True, cwd=path)
    except (FileNotFoundError, sp.CalledProcessError, AssertionError):
        shutil.rmtree(path, ignore_errors=True)
        sp.run(["git", "clone", proj.repo, path], check=True)

    if proj.commit is not None:
        sp.run(["git", "checkout", proj.commit], check=True, cwd=path)


def main():
    for proj in projs.values():
        checkout(proj)

    print("\nRunning Goose")
    sp.run(
        [
            "new/etc/update-goose-new.py",
            "--compile",
            "--std-lib",
            "--goose-examples",
            "--models",
            "--marshal",
            projs["marshal"].path(),
            "--std",
            projs["std"].path(),
            "--primitive",
            projs["primitive"].path(),
            "--etcd",
            projs["etcd"].path(),
            "--etcd-raft",
            projs["etcd-raft"].path(),
        ],
        check=True,
    )

    print("\nSeeing if anything is out of sync")
    sp.run(["git", "diff", "--exit-code"], check=True)
    print("\nSuccess!")


if __name__ == "__main__":
    main()
