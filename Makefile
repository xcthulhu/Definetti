.PHONY: build test configure configure-emacs clean app

build:
	stack build

TAGS: $(shell find src -name "*.hs") $(shell find app -name "*.hs")
	haskdogs --use-stack ON --hasktags-args "--etags"

test:
	stack test

hlint:
	stack test hlint --show-details=streaming

app: dist/build/shepherd/shepherd

dist/build/shepherd/shepherd: $(shell find src -name "*.hs") $(shell find app -name "*.hs")
	stack build shepherd

clean:
	rm -rf .stack-work/ dist-newstyle/
	cabal clean
