.PHONY: build test configure configure-emacs clean app

build:
	stack build

TAGS: $(shell find src -name "*.hs") $(shell find app -name "*.hs")
	haskdogs --use-stack ON --hasktags-args "--etags"


test:
	nix-shell --run 'cabal test --test-show-details=streaming'

hlint:
	nix-shell --run 'cabal test hlint --test-show-details=streaming'

# ghcid:
# 	nix-shell --run 'stack build && ghcid'

app: dist/build/shepherd/shepherd

dist/build/shepherd/shepherd: $(shell find src -name "*.hs") $(shell find app -name "*.hs")
	nix-shell --run 'cabal build shepherd'

clean:
	rm -rf .stack-work/ dist-newstyle/ dist
	cabal clean
