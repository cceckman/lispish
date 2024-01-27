#! /bin/sh
#
# Renders all targets.

set -eux

cargo build
for file in "$(find testdata -type f -name '*.lisp')"
do
  BASENAME="$(basename -s.lisp "$file")"
  <"$file" target/debug/lisp_to_graphviz \
    | dot -T svg \
  >"target/$BASENAME.svg"

  <"$file" target/debug/lisp_to_debug \
    >"target/$BASENAME.lisp" \
    2>"target/$BASENAME.debug"
done

# Run an HTTP server in the target directory,
# to view the results in a browser:
(cd target && python3 -m http.server)

