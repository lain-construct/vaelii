#!/usr/bin/env bash
# scripts/link-checkouts.sh [-f] [PREFIX] [SUFFIX] — wire up the dev-local
# checkout symlink so Leiningen resolves the foreign-format readers from live
# source instead of an installed snapshot jar:
#
#   checkouts/vaelii-foreign -> ../../vaelii-foreign
#
# The readers reach into `vaelii.impl.*`, which this engine is free to change. A
# checkout is how that break surfaces the moment it lands rather than at
# somebody's next `lein install`. A stale snapshot is the failure it avoids, and
# that failure is quiet: the jar does not fail loudly, it silently lacks whatever
# namespaces were added since.
#
# checkouts/ is gitignored, so the link is not committed — rerun after a fresh
# clone. Idempotent (ln -snf). A missing target is skipped with a WARN unless
# -f / --force is given (a dangling link is harmless and resolves once the
# sibling is cloned).
#
# **A checkout puts the plugin on EVERY command's classpath**, including
# `lein test`'s. That is safe for the suite, whose absence claims read the SOURCE
# TREE and the extension point rather than the classpath:
#
#   * `no-reader-ships-in-this-tree` stats src/vaelii/impl/foreign and
#     resources/vaelii/foreign.edn IN THIS REPO;
#   * `nothing-outside-the-extension-point-names-a-reader` greps this repo's src/ and test/;
#   * `the-extension-point-holds-no-compile-time-reference` reads the plugin file;
#   * the runtime tests use synthetic kinds (:no-such-format, :test-format) and a
#     temp-dir manifest, so a real plugin on the path is not what they measure.
#
# Measured 2026-07-31, one tree, the link as the only variable: **2408 tests /
# 120,061 assertions either way**, identical to the digit, 0 failures. The link
# adds no test and no assertion, and `lein test` does not pick up a checkout's
# test namespaces. vaelii.foreign-contract-test is green at 8 tests / 30
# assertions with the plugin on the path.
#
# What DOES change is that a linked build discovers five formats where the
# shipped build discovers none, so a foreign read that works on your machine may
# be the link rather than the code. That is a repl and browser concern, not a
# test one; `lein with-profile +with-foreign` remains the route for anyone
# without the sibling checked out, which is how a real consumer gets it
# (project.clj, docs/foreign.md).
#
# vaelii-foreign is the only sibling linked, because it is the only other
# published one. This script ships, so every repo it names has to be a repo the
# reader can clone — an unpublished sibling named here is a dead end for
# everybody who is not the maintainer. Those are wired up in profiles.clj, by
# hand, and profiles.clj is gitignored and local, which is where they belong.
#
# PREFIX / SUFFIX wrap the *target repo dir name* so a modified sibling clone can
# be linked while the checkout name stays fixed (Leiningen matches a checkout by
# the project.clj it finds, not by the directory name):
# `link-checkouts.sh "" -wip` points checkouts/vaelii-foreign at
# ../../vaelii-foreign-wip.
set -euo pipefail
cd "$(dirname "$0")/.."   # repo root
mkdir -p checkouts

force=0
while [[ "${1:-}" == -* ]]; do
  case "$1" in
    -f|--force) force=1; shift ;;
    -h|--help)  sed -n '2,17p' "$0"; exit 0 ;;
    --) shift; break ;;
    *)  echo "unknown option: $1" >&2; exit 2 ;;
  esac
done

prefix="${1:-}"
suffix="${2:-}"

# $1 = checkout name (fixed — Leiningen resolves the artifact against it)
# $2 = repo dir name (prefix/suffix applied here)
link() {
  local name="$1" repo="$2"
  local target="../../${prefix}${repo}${suffix}"
  # target is relative to checkouts/, so test it from there.
  if [[ $force -eq 0 && ! -e "checkouts/$target" ]]; then
    echo "WARN: skipping checkouts/$name -> $target (target missing; -f to link anyway)" >&2
    return
  fi
  ln -snf "$target" "checkouts/$name"
  echo "linked checkouts/$name -> $target"
}

link vaelii-foreign vaelii-foreign
