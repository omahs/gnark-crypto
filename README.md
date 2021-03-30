# gnark-crypto

[![License](https://img.shields.io/badge/license-Apache%202-blue)](LICENSE)  [![Go Report Card](https://goreportcard.com/badge/github.com/consensys/gnark-crypto)](https://goreportcard.com/badge/github.com/consensys/gnark-crypto) [![PkgGoDev](https://pkg.go.dev/badge/mod/github.com/consensys/gnark-crypto)](https://pkg.go.dev/mod/github.com/consensys/gnark-crypto)


`gnark-crypto` is actively developed and maintained by the team (zkteam@consensys.net) behind:
* [`gnark`: a framework to execute (and verify) algorithms in zero-knowledge](https://github.com/consensys/gnark) 


## Warning
**`gnark-crypto` has not been audited and is provided as-is, use at your own risk. In particular, `gnark-crypto` makes no security guarantees such as constant time implementation or side-channel attack resistance.**

`gnark-crypto` is optimized for 64bits architectures (x86 `amd64`) and tested on Unix (Linux / macOS).

## Documentation

[![PkgGoDev](https://pkg.go.dev/badge/mod/github.com/consensys/gnark-crypto)](https://pkg.go.dev/mod/github.com/consensys/gnark-crypto)

Packages:

| Package  | Description |
| ------------- | ------------- |
| curve  |  provides implementation of BN254 (Ethereum), BLS12-381(ZCash), BLS377 (ZEXE) and BW6-761 (EC supporting pairing on BLS377 field of definition), alongside with their twisted edwards "companion" curves. provides Pairing, Multi Exponentiation, FFT algorithms  |
| crypto  | provides implementation of MiMC and EdDSA (on the twisted edwards curve) |
| field  |  provides code generation for efficient field arithmetic for any moduli |


## Getting started

### Go version

`gnark-crypto` is tested with the last 2 major releases of Go (1.14 and 1.15).

### Install `gnark-crypto` 

```bash
go get github.com/consensys/gnark-crypto
```

Note if that if you use go modules, in `go.mod` the module path is case sensitive (use `consensys` and not `ConsenSys`).

### Documentation
[![PkgGoDev](https://pkg.go.dev/badge/mod/github.com/consensys/gnark-crypto)](https://pkg.go.dev/mod/github.com/consensys/gnark-crypto)

The APIs are consistent accross the curves. For example, [here is `bn254` godoc](https://pkg.go.dev/github.com/consensys/gnark-crypto/bn254#pkg-overview).

## Benchmarks

TODO point to https://hackmd.io/@zkteam/eccbench

Here are our measurements comparing `gnark-crypto` (and [`goff` our finite field library](https://github.com/consensys/gnark-crypto)) with [`mcl`](https://github.com/herumi/mcl).

These benchmarks ran on a AWS z1d.3xlarge instance, with hyperthreading disabled. 

|bn254|mcl(ns/op)|gnark-crypto & goff (ns/op)|
| -------- | -------- | -------- |
|Fp::Add	|3.32|	3.44|
|Fp::Mul	|18.43|	16.1|
|Fp::Square	|18.64|	15.1|
|Fp::Inv	|690.55	|2080*|
|Fp::Pow	|6485|	7440*|
|G1::ScalarMul|	41394|	56900|
|G1::Add	|213|	224|
|G1::Double	|155|	178|
|G2::ScalarMul|	88423|	141000|
|G2::Add	|598|	871|
|G2::Double	|371|	386|
|Pairing	|478244	|489258|


----


|bls381|mcl(ns/op)|gnark-crypto & goff (ns/op)|
| -------- | -------- | -------- |
|Fp::Add	|5.42|	4.6|
|Fp::Mul	|33.63|	29.3|
|Fp::Square	|33.86|	27|
|Fp::Inv	|1536	|4390*|
|Fp::Pow	|18039|	18300*|
|G1::ScalarMul|	76799|	91500|
|G1::Add	|424|	389|
|G1::Double	|308|	301|
|G2::ScalarMul|	159068|	273000|
|G2::Add	|1162|	1240|
|G2::Double	|727|	799|
|Pairing	|676513	|707984|

*note that some routines don't have assembly implementation in `goff` yet.


## Versioning

We use [SemVer](http://semver.org/) for versioning. For the versions available, see the [tags on this repository](https://github.com/consensys/gnark-crypto/tags). 


## License

This project is licensed under the Apache 2 License - see the [LICENSE](LICENSE) file for details
