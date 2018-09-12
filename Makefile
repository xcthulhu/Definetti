.PHONY: build test configure configure-repl clean

build:
	cabal build

test:
	cabal test

configure:
	nix-shell --run "cabal configure --enable-tests"

configure-repl:
	nix-shell --run "cabal configure -flibrary-only"

clean:
	cabal clean
