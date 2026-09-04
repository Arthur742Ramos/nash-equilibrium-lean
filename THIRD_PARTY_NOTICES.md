# Third-party notices

The files under `Gametheory/` are included from the Lean development
[Formalizing Scarf, Brouwer, and Nash in Lean](https://github.com/math-xmum/Brouwer),
commit `09941e849a81e520cc0cc53220f10f8e5f4768e`.

The included files are `Scarf.lean`, `ScarfPath.lean`, `Brouwer.lean`, and
`Brouwer_product.lean`. They provide the kernel-checked Scarf-to-Brouwer and
product-of-simplices fixed-point theorems used by
`NashEquilibrium.MixedBrouwer`. The native bridge from those theorems to this
repository's `MixedGame` and `MixedProfile` definitions is the
repository-specific adapter. The upstream source is used with attribution
under the MIT License.

Copyright (c) 2025 Math_XMUM

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
