{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.default = pkgs.mkShell {
        packages = with pkgs; [ 
          bashInteractive
          elan
          cadical
          texlive.combined.scheme-full
          texlab
          fontconfig
          gcc
          python3
        ];

        FONTCONFIG_FILE = pkgs.makeFontsConf { fontDirectories = [
            "/Library/Fonts"
            "/System/Library/Fonts"
            "/Users/wojtek/Library/Fonts"
            pkgs.iosevka
          ];
        };

        # Create a python virtual environment with eznf and lark
        venvDir = "./.venv";
        buildInputs = with pkgs.python3Packages; [
          python
          venvShellHook
        ];

        postVenvCreation = ''
          unset SOURCE_DATE_EPOCH
          pip install eznf lark
        '';
      };
    });
}
