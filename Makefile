.PHONY: build test configure configure-repl clean

build:
	cabal build

configure:
	nix-shell --run 'cabal configure --enable-tests'

configure-with-coverage:
	nix-shell --run 'cabal configure --enable-tests --enable-coverage'

configure-app:
	nix-shell --run 'cabal configure -fenable-cli-app --enable-tests'

test:
	cabal test --show-details=streaming

hlint:
	cabal test hlint --show-details=streaming

test-continuous:
	nix-shell --run 'ghcid -c "cabal repl definetti-test" --test "Main.main"'

app: dist/build/shepherd/shepherd

dist/build/shepherd/shepherd: $(shell find src -name "*.hs") $(shell find app -name "*.hs")
	make configure-app
	cabal build shepherd


clean:
	cabal clean
