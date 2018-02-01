definetti
=========

### Configure:

```sh
nix-shell --command "cabal configure --enable-tests"
```

### Build:

```sh
cabal build
```

### Test:

```sh
cabal test
```

### Regenerate Nix file:

After changing `definetti.cabal`, you should run:

```sh
cabal2nix . >definetti.nix
nix-shell --command "cabal configure --enable-tests"
```

and commit the change to the updated `definetti.nix` file.
