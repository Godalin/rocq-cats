#!/bin/sh
set -eu

toolchain=$1
test_dir=$(mktemp -d)
trap 'rm -rf "$test_dir"' EXIT HUP INT TERM

cat > "$test_dir/opam" <<'STUB'
#!/bin/sh
test "$1" = list || exit 2
shift
test "$1" = --switch=fixture || exit 2
shift
test "$1" = --color=never || exit 2
test "${OPAMCOLOR:-}" = always || exit 2
test "${CLICOLOR_FORCE:-}" = 1 || exit 2
test "${OPAM_TEST_EXIT:-0}" = 0 || exit "$OPAM_TEST_EXIT"
cat "$OPAM_TEST_PACKAGES"
STUB
chmod +x "$test_dir/opam"
PATH="$test_dir:$PATH"
export PATH OPAM_TEST_PACKAGES

cat > "$test_dir/expected" <<'PACKAGES'
conf-gmp.5
ocaml.5.3.0
rocq-core.9.3.0
PACKAGES

# The two CI hosts differ only by a Linux system-header probe.
for host in macos linux; do
  OPAM_TEST_PACKAGES="$test_dir/$host"
  if test "$host" = linux; then
    printf 'conf-linux-libc-dev.0\n' > "$OPAM_TEST_PACKAGES"
    cat "$test_dir/expected" >> "$OPAM_TEST_PACKAGES"
  else
    cp "$test_dir/expected" "$OPAM_TEST_PACKAGES"
  fi
  OPAMCOLOR=always CLICOLOR_FORCE=1 sh "$toolchain" --switch=fixture \
    > "$test_dir/actual"
  diff -u "$test_dir/expected" "$test_dir/actual"
done

# A failed package query must not become a successful empty inventory.
if OPAMCOLOR=always CLICOLOR_FORCE=1 OPAM_TEST_EXIT=17 \
    sh "$toolchain" --switch=fixture > "$test_dir/failed"; then
  echo 'The inventory hid an opam failure' >&2
  exit 1
else
  test "$?" -eq 17
fi
