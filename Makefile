.PHONY: build test configure configure-emacs clean app

build:
	cabal build

configure:
	nix-shell --run 'cabal configure --enable-tests'

configure-with-coverage:
	nix-shell --run 'cabal configure --enable-tests --enable-coverage'

configure-emacs:
	nix-shell --run 'cabal configure -flibrary-only'

test:
	cabal test --show-details=streaming

hlint:
	cabal test hlint --show-details=streaming

ghcid:
	nix-shell --run 'stack build && ghcid'

app: dist/build/shepherd/shepherd

dist/build/shepherd/shepherd: $(shell find src -name "*.hs") $(shell find app -name "*.hs")
	cabal build shepherd

clean:
	rm -rf .stack-work/ dist-newstyle/
	cabal clean
