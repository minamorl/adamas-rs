#!/bin/sh
# The one thing `cargo test` cannot see.
#
# Add a single line inside `src/kernel/` that hands out `Thm { theory, hyps,
# concl }` and every behaviour test in this crate still passes — measured: all
# of them, plus the doctests. That is not a gap in the tests. What such a line
# breaks is a *compile-time* boundary, and a test can only observe values.
#
# The README's claim is that the kernel does not grow when the library does.
# This is where that claim is checked. A change under `src/kernel/` has to be
# said out loud: put
#
#     kernel-frontier: <why>
#
# in a commit message on the branch. Then this passes, with the reason quoted
# in the log. Otherwise it fails, however green the tests are.
set -eu
base="${1:?usage: kernel-frontier.sh <base-ref>}"

lines=$(cat src/kernel/*.rs | wc -l | tr -d ' ')
changed=$(git diff --name-only "$base"...HEAD -- src/kernel/)

if [ -z "$changed" ]; then
  printf 'kernel untouched at %s lines; the library grew on its own.\n' "$lines"
  exit 0
fi

reason=$(git log "$base..HEAD" --format=%B | grep '^kernel-frontier: ' || true)
if [ -n "$reason" ]; then
  printf 'the kernel changed, deliberately, and now stands at %s lines:\n\n' "$lines"
  printf '%s\n' "$reason"
  printf '\nfiles:\n%s\n' "$changed"
  exit 0
fi

printf 'the kernel changed and no commit on this branch says why:\n\n' >&2
printf '%s\n' "$changed" >&2
printf '\nIf that is deliberate, put a line\n\n    kernel-frontier: <why>\n\n' >&2
printf 'in a commit message here. If it is not, the tests will not tell you:\n' >&2
printf 'they went green with the boundary open.\n' >&2
exit 1
