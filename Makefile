.PHONY: build test configure configure-repl clean

build:
	cabal build

test:
	cabal test --show-details=streaming

configure:
	nix-shell --run "cabal configure --enable-tests"

configure-with-coverage:
	nix-shell --run "cabal configure --enable-tests --enable-coverage"

configure-repl:
	nix-shell --run "cabal configure -flibrary-only"

clean:
	cabal clean
