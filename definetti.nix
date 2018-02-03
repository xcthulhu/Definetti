{ mkDerivation, base, containers, hlint, optparse-applicative
, QuickCheck, stdenv, tasty, tasty-hunit, tasty-quickcheck
}:
mkDerivation {
  pname = "definetti";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [ base containers ];
  executableHaskellDepends = [ base optparse-applicative ];
  testHaskellDepends = [
    base containers hlint QuickCheck tasty tasty-hunit tasty-quickcheck
  ];
  homepage = "https://github.com/githubuser/definetti#readme";
  license = stdenv.lib.licenses.unfree;
}
