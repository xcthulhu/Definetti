definetti
=========

### Configure:

```sh
nix-shell --command "cabal configure --enable-tests --enable-coverage"
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
nix-env -iA nixpkgs.haskellPackages.cabal2nix
cabal2nix . >definetti.nix
nix-shell --command "cabal configure --enable-tests --enable-coverage"
```

and commit the change to the updated `definetti.nix` file.
