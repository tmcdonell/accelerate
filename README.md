<div align="center">
<img width="450" src="https://github.com/tmcdonell/accelerate/raw/master/images/accelerate-logo-text-v.png?raw=true" alt="henlo, my name is Theia"/>

# High-performance parallel arrays for Haskell

[![CI](https://github.com/tmcdonell/accelerate/actions/workflows/ci.yml/badge.svg)](https://github.com/tmcdonell/accelerate/actions/workflows/ci.yml)
[![Hackage](https://img.shields.io/hackage/v/accelerate.svg)](https://hackage.haskell.org/package/accelerate)

</div>

`Data.Array.Accelerate` defines an embedded language of array computations for high-performance computing in Haskell. Computations on multi-dimensional, regular arrays are expressed in the form of parameterised collective operations (such as maps, reductions, and permutations). These computations are online-compiled and executed on a range of architectures.

For more details, we have a few academic papers:

 * [Accelerating Haskell Array Codes with Multicore GPUs](https://github.com/tmcdonell/tmcdonell.github.io/raw/master/papers/acc-cuda-damp2011.pdf)
 * [Optimising Purely Functional GPU Programs](https://github.com/tmcdonell/tmcdonell.github.io/raw/master/papers/acc-optim-icfp2013.pdf) ([slides](https://speakerdeck.com/tmcdonell/optimising-purely-functional-gpu-programs))
 * [Embedding Foreign Code](https://github.com/tmcdonell/tmcdonell.github.io/raw/master/papers/acc-ffi-padl2014.pdf)
 * [Type-safe Runtime Code Generation: Accelerate to LLVM](https://github.com/tmcdonell/tmcdonell.github.io/raw/master/papers/acc-llvm-haskell2015.pdf) ([slides](https://speakerdeck.com/tmcdonell/type-safe-runtime-code-generation-accelerate-to-llvm)), ([video](https://www.youtube.com/watch?v=snXhXA5noVc))
 * [Streaming Irregular Arrays](https://github.com/tmcdonell/tmcdonell.github.io/raw/master/papers/acc-seq2-haskell2017.pdf) ([video](https://www.youtube.com/watch?v=QIWSqp7AaNo))
 * [Embedded Pattern Matching](https://github.com/tmcdonell/tmcdonell.github.io/raw/master/papers/acc-pattern.pdf) ([slides](https://speakerdeck.com/tmcdonell/annotating-deeply-embedded-languages), [video](https://youtu.be/Y1s28Sm5s8E))

and presentations:

 * [FHPNC 2019 Keynote: Functional High-Performance Computing](https://speakerdeck.com/tmcdonell/functional-high-performance-computing)
 * [Embedded Languages for High-Performance Computing in Haskell](https://speakerdeck.com/mchakravarty/embedded-languages-for-high-performance-computing-in-haskell)
 * [GPGPU Programming in Haskell with Accelerate](https://speakerdeck.com/tmcdonell/gpgpu-programming-in-haskell-with-accelerate) ([video](http://youtu.be/ARqE4yT2Z0o)) ([workshop](https://speakerdeck.com/tmcdonell/gpgpu-programming-in-haskell-with-accelerate-workshop))

Chapter 6 of Simon Marlow's book [Parallel and Concurrent Programming in Haskell](http://chimera.labs.oreilly.com/books/1230000000929) contains a tutorial introduction to Accelerate.

[Trevor's PhD thesis](https://github.com/tmcdonell/tmcdonell.github.io/raw/master/papers/TrevorMcDonell_PhD_Thesis.pdf) details the design and implementation of frontend optimisations and CUDA backend.


**Table of Contents**

- [An Embedded Language for Accelerated Array Computations](#an-embedded-language-for-accelerated-array-computations)
  - [A simple example](#a-simple-example)
  - [Availability](#availability)
  - [Additional components](#additional-components)
  - [Requirements](#requirements)
  - [Documentation](#documentation)
  - [Examples](#examples)
  - [Who are we?](#who-are-we)
  - [Mailing list and contacts](#mailing-list-and-contacts)
  - [Citing Accelerate](#citing-accelerate)
  - [What's missing?](#whats-missing)

A simple example
----------------

As a simple example, consider the computation of a dot product of two vectors of single-precision floating-point numbers:

    dotp :: Acc (Vector Float) -> Acc (Vector Float) -> Acc (Scalar Float)
    dotp xs ys = fold (+) 0 (zipWith (*) xs ys)

Except for the type, this code is almost the same as the corresponding Haskell code on lists of floats. The types indicate that the computation may be online-compiled for performance; for example, using `Data.Array.Accelerate.LLVM.PTX.run` it may be on-the-fly off-loaded to a GPU.

Availability
------------

Package _Accelerate_ is available from:

 * Hackage: [accelerate](http://hackage.haskell.org/package/accelerate) - install with `cabal install accelerate`
 * GitHub: [tmcdonell/accelerate](https://github.com/tmcdonell/accelerate) - get the source with `git clone https://github.com/tmcdonell/accelerate.git`

To install the Haskell toolchain try [GHCup](https://www.haskell.org/ghcup/).

Additional components
---------------------

The following add-ons are available as separate packages:

  * [accelerate-llvm-native](https://github.com/tmcdonell/accelerate-llvm): Backend targeting multicore CPUs
  * [accelerate-llvm-ptx](https://github.com/tmcdonell/accelerate-llvm): Backend targeting CUDA-enabled NVIDIA GPUs. Requires a GPU with compute capability 2.0 or greater (see the [table on Wikipedia](https://en.wikipedia.org/wiki/CUDA#Supported_GPUs))
  * [accelerate-examples](https://github.com/tmcdonell/accelerate-examples): Computational kernels and applications showcasing the use of Accelerate as well as a regression test suite (supporting function and performance testing)
  * Conversion between various formats:
    * [accelerate-io](https://hackage.haskell.org/package/accelerate-io): For copying data directly between raw pointers
    * [accelerate-io-array](https://hackage.haskell.org/package/accelerate-io-array): Immutable arrays
    * [accelerate-io-bmp](https://hackage.haskell.org/package/accelerate-io-bmp): Uncompressed BMP image files
    * [accelerate-io-bytestring](https://hackage.haskell.org/package/accelerate-io-bytestring): Compact, immutable binary data
    * [accelerate-io-cereal](https://hackage.haskell.org/package/accelerate-io-cereal): Binary serialisation of arrays using [cereal](https://hackage.haskell.org/package/cereal)
    * [accelerate-io-JuicyPixels](https://hackage.haskell.org/package/accelerate-io-JuicyPixels): Images in various pixel formats
    * [accelerate-io-repa](https://hackage.haskell.org/package/accelerate-io-repa): Another Haskell library for high-performance parallel arrays
    * [accelerate-io-serialise](https://hackage.haskell.org/package/accelerate-io-serialise): Binary serialisation of arrays using [serialise](https://hackage.haskell.org/package/serialise)
    * [accelerate-io-vector](https://hackage.haskell.org/package/accelerate-io-vector): Efficient boxed and unboxed one-dimensional arrays
  * [accelerate-fft](https://github.com/tmcdonell/accelerate-fft): Fast Fourier transform implementation, with FFI bindings to optimised implementations
  * [accelerate-blas](https://github.com/tmcdonell/accelerate-blas): BLAS and LAPACK operations, with FFI bindings to optimised implementations
  * [accelerate-bignum](https://github.com/tmcdonell/accelerate-bignum): Fixed-width large integer arithmetic
  * [colour-accelerate](https://github.com/tmcdonell/colour-accelerate): Colour representations in Accelerate (RGB, sRGB, HSV, and HSL)
  * [containers-accelerate](http://hackage.haskell.org/package/containers-accelerate): Hashing-based container types
  * [gloss-accelerate](https://github.com/tmcdonell/gloss-accelerate): Generate [gloss](https://hackage.haskell.org/package/gloss) pictures from Accelerate
  * [gloss-raster-accelerate](https://github.com/tmcdonell/gloss-raster-accelerate): Parallel rendering of raster images and animations
  * [hashable-accelerate](http://hackage.haskell.org/package/hashable-accelerate): A class for types which can be converted into a hash value
  * [lens-accelerate](https://github.com/tmcdonell/lens-accelerate): [Lens](https://hackage.haskell.org/package/lens) operators for Accelerate types
  * [linear-accelerate](https://github.com/tmcdonell/linear-accelerate): [Linear](https://hackage.haskell.org/package/linear) vector spaces in Accelerate
  * [mwc-random-accelerate](https://github.com/tmcdonell/mwc-random-accelerate): Generate Accelerate arrays filled with high quality pseudorandom numbers
  * [numeric-prelude-accelerate](https://github.com/tmcdonell/numeric-prelude-accelerate): Lifting the [numeric-prelude](https://hackage.haskell.org/package/numeric-prelude) to Accelerate
  * [wigner-ville-accelerate](https://github.com/Haskell-mouse/wigner-ville-accelerate): Wigner-Ville time-frequency distribution.

Install them from Hackage with `cabal install PACKAGENAME`.


Documentation
-------------

  * Haddock documentation is included and linked with the individual package releases on [Hackage](https://hackage.haskell.org/package/accelerate)
  <!-- * Haddock documentation for in-development components can be found [here](http://tmcdonell-bot.github.io/accelerate-travis-buildbot/). -->
  * The idea behind the HOAS (higher-order abstract syntax) to de-Bruijn conversion used in the library is [described separately](https://github.com/mchakravarty/hoas-conv)

Examples
--------

### accelerate-examples

The [accelerate-examples][accelerate-examples] package provides a range of computational kernels and a few complete applications. To install these from Hackage, issue `cabal install accelerate-examples`. The examples include:

  * An implementation of [canny edge detection](https://en.wikipedia.org/wiki/Canny_edge_detector)
  * An interactive [mandelbrot set](https://en.wikipedia.org/wiki/Mandelbrot_set) generator
  * An [N-body simulation](https://en.wikipedia.org/wiki/N-body) of gravitational attraction between solid particles
  * An implementation of the [PageRank](https://en.wikipedia.org/wiki/Pagerank) algorithm
  * A simple [ray-tracer](https://en.wikipedia.org/wiki/Ray_tracing)
  * A particle based simulation of stable fluid flows
  * A cellular automata simulation
  * A "password recovery" tool, for dictionary lookup of MD5 hashes

[![Mandelbrot](https://i.imgur.com/5Tbsp1j.jpg "accelerate-mandelbrot")](https://i.imgur.com/RgXRqsc.jpg)
[![Raytracer](https://i.imgur.com/7ohhKm9.jpg "accelerate-ray")](https://i.imgur.com/ZNEGEJK.jpg)

<!--
<video width=400 height=300 controls=false autoplay loop>
  <source="http://www.cse.unsw.edu.au/~tmcdonell/images/ray.mp4" type="video/mp4">
</video>
-->


### LULESH

[LULESH-accelerate](https://github.com/tmcdonell/lulesh-accelerate) is in implementation of the Livermore Unstructured Lagrangian Explicit Shock Hydrodynamics (LULESH) mini-app. [LULESH](https://codesign.llnl.gov/lulesh.php) represents a typical hydrodynamics code such as [ALE3D](https://wci.llnl.gov/simulation/computer-codes/ale3d), but is a highly simplified application, hard-coded to solve the Sedov blast problem on an unstructured hexahedron mesh.

![LULESH mesh](https://i.imgur.com/bIkODKd.jpg)


### Additional examples

Accelerate users have also built some substantial applications of their own.
Please feel free to add your own examples!

  * Jonathan Fraser, [GPUVAC](https://github.com/GeneralFusion/gpuvac): An explicit advection magnetohydrodynamics simulation
  * David van Balen, [Sudokus](https://github.com/dpvanbalen/Sudokus): A sudoku solver
  * Trevor L. McDonell, [lol-accelerate](https://github.com/tmcdonell/lol-accelerate): A backend to the Λ ○ λ ([Lol](https://hackage.haskell.org/package/lol)) library for ring-based lattice cryptography
  * Henning Thielemann, [patch-image](http://hackage.haskell.org/package/patch-image): Combine a collage of overlapping images
  * apunktbau, [bildpunkt](https://github.com/abau/bildpunkt): A ray-marching distance field renderer
  * klarh, [hasdy](https://github.com/klarh/hasdy): Molecular dynamics in Haskell using Accelerate
  * Alexandros Gremm used Accelerate as part of the [2014 CSCS summer school](http://user.cscs.ch/blog/2014/cscs_usi_summer_school_2014_30_june_10_july_2014_in_serpiano_tessin/index.html) ([code](https://github.com/agremm/cscs))


Who are we?
-----------

The Accelerate team (past and present) consists of:

  * Manuel M T Chakravarty ([@mchakravarty])  <!-- 2008..2017 -->
  * Gabriele Keller ([@gckeller])             <!-- 2008..     -->
  * Trevor L. McDonell ([@tmcdonell])         <!-- 2009..     -->
  * Robert Clifton-Everest ([@robeverest])    <!-- 2013..     -->
  * Frederik M. Madsen ([@fmma])              <!-- 2014       -->
  * Ryan R. Newton ([@rrnewton])              <!-- 2012..2013 -->
  * Joshua Meredith ([@JoshMeredith])         <!-- 2018..     -->
  * Ben Lever ([@blever])                     <!-- 2010..2011 -->
  * Sean Seefried ([@sseefried])              <!-- 2010..2011 -->
  * Ivo Gabe de Wolff ([@ivogabe])            <!-- 2019..     -->
  * David van Balen ([@dpvanbalen])           <!-- 2020..     -->
  * Tom Smeding ([@tomsmeding])               <!-- 2021..     -->
  * Robbert van der Helm ([@robbert-vdh])     <!-- 2022       -->

The architect and leader of the Accelerate project is Trevor L. McDonell <trevor.mcdonell@gmail.com>. Please feel free to reach out to me!


Mailing list and contacts
-------------------------

  * [Bug reports and issues tracking](https://github.com/tmcdonell/accelerate/issues)
  * [Questions and discussion](https://github.com/tmcdonell/accelerate/discussions)
  * [`accelerate-haskell@googlegroups.com`](mailto:accelerate-haskell@googlegroups.com) mailing list ([sign-up](http://groups.google.com/group/accelerate-haskell))


What's missing?
---------------

Here is a list of features that are currently missing:

 * Preliminary API (parts of the API may still change in subsequent releases)
 * Many more features... [contact us](mailto:trevor.mcdonell@gmail.com)!

  [@tmcdonell]:                 https://github.com/tmcdonell
  [@mchakravarty]:              https://github.com/mchakravarty
  [@gckeller]:                  https://github.com/gckeller
  [@robeverest]:                https://github.com/robeverest
  [@fmma]:                      https://github.com/fmma
  [@rrnewton]:                  https://github.com/rrnewton
  [@JoshMeredith]:              https://github.com/JoshMeredith
  [@blever]:                    https://github.com/blever
  [@sseefried]:                 https://github.com/sseefried
  [@ivogabe]:                   https://github.com/ivogabe
  [@dpvanbalen]:                https://github.com/dpvanbalen
  [@tomsmeding]:                https://github.com/tomsmeding

  [accelerate-cuda]:            https://github.com/tmcdonell/accelerate-cuda
  [accelerate-backend-kit]:     https://github.com/AccelerateHS/accelerate-backend-kit
  [accelerate-buildbot]:        https://github.com/AccelerateHS/accelerate-buildbot
  [accelerate-repa]:            https://github.com/blambo/accelerate-repa
  [accelerate-opencl]:          https://github.com/hiPERFIT/accelerate-opencl
  [HOAS-conv]:                  https://web.archive.org/web/20180805092417/http://www.cse.unsw.edu.au/~chak/haskell/term-conv/

