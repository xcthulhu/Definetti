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

test-continuous:
	stack build definetti:test:definetti-test
	ghcid -c="stack ghci definetti:lib definetti:test:definetti-test --ghci-options=-fobject-code" --test ":main"

app: dist/build/shepherd/shepherd

dist/build/shepherd/shepherd: $(shell find src -name "*.hs") $(shell find app -name "*.hs")
	cabal build shepherd

clean:
	rm -rf .stack-work/ dist-newstyle/
	cabal clean
