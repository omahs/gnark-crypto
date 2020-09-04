// Copyright 2020 ConsenSys AG
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Code generated by goff (v0.3.3) DO NOT EDIT

// Package fp contains field arithmetic operations
package fp

// q'[0], see montgommery multiplication algorithm
// used in assembly code
var qElementInv0 uint64 = 9586122913090633727

//go:noescape
func add(res, x, y *Element)

//go:noescape
func sub(res, x, y *Element)

//go:noescape
func neg(res, x *Element)

//go:noescape
func double(res, x *Element)

//go:noescape
func mul(res, x, y *Element)

//go:noescape
func square(res, x *Element)

//go:noescape
func fromMont(res *Element)

//go:noescape
func reduce(res *Element)
