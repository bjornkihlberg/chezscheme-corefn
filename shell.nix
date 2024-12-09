with (import <nixpkgs> {});

mkShell {
  nativeBuildInputs = [
    chez
    purescript
  ];
}
