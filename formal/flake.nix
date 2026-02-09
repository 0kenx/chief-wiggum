{
  description = "TLA+ formal model of Chief Wiggum — Apalache + Z3 dev environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Apalache is not in nixpkgs — fetch the pre-built release and wrap it.
        # It's a JVM app distributed as a tgz containing bin/apalache-mc.
        apalacheVersion = "0.52.2";
        apalache = pkgs.stdenv.mkDerivation {
          pname = "apalache";
          version = apalacheVersion;

          src = pkgs.fetchurl {
            url = "https://github.com/apalache-mc/apalache/releases/download/v${apalacheVersion}/apalache-${apalacheVersion}.tgz";
            sha256 = "e0ebea7e45c8f99df8d92f2755101dda84ab71df06d1ec3a21955d3b53a886e2";
          };

          nativeBuildInputs = [ pkgs.makeWrapper ];
          buildInputs = [ pkgs.jdk17_headless ];

          dontConfigure = true;
          dontBuild = true;

          unpackPhase = ''
            mkdir -p src
            tar xzf $src -C src --strip-components=1
          '';

          installPhase = ''
            mkdir -p $out/share/apalache $out/bin
            cp -r src/lib $out/share/apalache/
            cp -r src/bin $out/share/apalache/

            makeWrapper $out/share/apalache/bin/apalache-mc $out/bin/apalache-mc \
              --set JAVA_HOME "${pkgs.jdk17_headless}" \
              --prefix PATH : "${pkgs.jdk17_headless}/bin"
          '';
        };
      in {
        packages.apalache = apalache;

        devShells.default = pkgs.mkShell {
          packages = [ apalache pkgs.z3 ];
        };
      });
}
