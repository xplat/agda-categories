{ }:

let
  pkgs =
    import (builtins.fetchTarball {
      url = "https://github.com/nixos/nixpkgs/archive/f034fde6e5a8976410cc7c7000d63c5aabd3f94c.tar.gz";
      sha256 = "0x4vq8x6h5vri0bn3vz1dszcyg6i1m8vjwbwlm4cn36pcspdhrnj" ;
    }) {};
in pkgs
