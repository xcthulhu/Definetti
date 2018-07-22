Definetti
=========

Before running any code, you will need to go through a configuration step.

See below for details.

### Configure:

```sh
nix-shell --command "cabal configure --enable-tests --enable-coverage"
```

Note: after changing `definetti.cabal`, you will need to rerun configuration.

### Build:

```sh
cabal build
```

### Test:

```sh
cabal test
```