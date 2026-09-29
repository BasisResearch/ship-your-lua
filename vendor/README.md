# Vendored sources

`lua-5.4.7/` is the unmodified Lua 5.4.7 release tarball
(https://www.lua.org/ftp/lua-5.4.7.tar.gz, sha256
`9fbf5e28ef86c69858f6d3d34eccc32e911c1a28b4120ff3e84aaa70cfbf1e30`),
MIT licence in `lua-5.4.7/LICENSE` (copied verbatim from `src/lua.h`).
Bare-metal configuration is done without editing it: `c/src/baremetal.h`
is force-included (`-include`) and `c/Makefile` sets the flags.
