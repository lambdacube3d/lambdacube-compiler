
# v0.6

-   new features
    -   support mutual constant and function definitions
    -   support pattern type annotations
    -   support guards + where
    -   support view patterns
    -   support pattern guards
    -   support as-patterns
    -   implement constraint kinds
    -   implement pattern match reachability and exhaustiveness warnings 
    -   allow pattern match on tuple types
    -   support parsing only
    -   support printing desugared source code
-   improvements
    -   improve pretty printing
    -   better presentation of types in editor tooltips
    -   better error messages (e.g. for mismatching operator fixities)
    -   speedup the builtin interpreter in the compiler
-   bugfixes
    -   fix local function handling
    -   fix parens around operators
    -   fix parsing of operator definitions
    -   fix parsing of sections
    -   fix parsing of literals
    -   fix switching to type namespace after @
    -   fix a bug in escape code parsing
-   documentation
    -   reorganise and cleanup the compiler sources
    -   begin to write developer's guide
    -   documentation on pattern match compilation
-   dependencies
    -   use megaparsec 5.0
    -   switch to ansi-wl-pprint
    -   allow newer base, optparse-applicative and QuickCheck libraries
-   other
    -   move the TODOs to Trello: https://trello.com/b/TcuVPBAR/lambdacube3d
    -   work on prototypes (reducer, lammachine, inspector)


# v0.5

-   compiler
    -   support local pattern matching functions
    -   support recursive local definitions
    -   more polymorph type for equality constraints
        (~) :: forall a . a -> a -> Type
    -   tuples are representated as heterogeneous lists
    -   support one-element tuple syntax: (( element ))
    -   reduction: don't overnormalize (String -/-> [Char])
    -   compiler optimization: names have Int identifiers
-   libraries/OpenGL API
    -   use the advantage of heterogeneous lists
        (simplified and more complete type family instances)
    -   needed to explicitly denote one-element attribute tuples
    -   set programmable point size with ProgramPointSize
    -   use lists instead of streams
    -   rename
        -   fetch_ --> fetch; fetchArrays_ --> fetchArrays
        -   zeroComp --> zero; oneComp --> one
-   codegen
    -   generate functions in shaders (previously functions were inlined)
    -   normalized variable names in the generated pipeline
    -   optimization: remove duplicate shader programs
    -   pretty printed shader programs
    -   include compiler version in the generated pipeline as a string info field
-   testenv
    -   performance benchmarks (time and memory consumption)
-   other
    -   parsec dependency changed to megaparsec
    -   registered on stackage too (next to HackageDB)


# v0.4 - tagged on Feb 5, 2016

-   compiler
    -   support type synonyms
    -   support simple import lists (hiding + explicit)
    -   support multiple guards
    -   handle constructor operator fixities, also in patterns
    -   definitions are allowed in any order (not just bottom-up)
    -   desugar node definitions (more robust, previously node definition handling was ad-hoc)
    -   support qualified module imports
    -   better tooltip ranges & types
    -   bugfix: fix looping in type checking of recursive definitions
-   compiler optimization
    -   separate types and values (vs. church style lambda)
    -   separate use of neutral terms
    -   erease lambda variable type
    -   erease univ. pol. arguments of constructors
    -   erease univ. pol. arguments of case functions
    -   speed up 'eval' function
    -   tried to speedup with cache max. de bruin indices
    -   use less 'try' in parser
-   libraries
    -   always put base library modules to include path
    -   OpenGL API: simplify CullMode: remove FrontFace it is always ccw
    -   OpenGL API: simplify Depth images handling
-   testenv
    -   language feature tests framework
-   other
    -   released on HackageDB


# v0.3 - tagged on Jan 18, 2016

-   compiler
    -   complete rewrite from scratch
    -   use De Bruijn indices instead of String names
    -   pattern match compilation
    -   compositional type inference is replaced by a zipper-based approach
        which plays better together with dependent types
-   libraries/OpenGL API
    -   interpolation handling is decoupled from vertex shader descriptions
    -   introduce Stream data type; use just two types of streams instead of 4
-   testenv
    -   use Travis CI (continuous integration) with a docker image
    -   timeout for tests


# first DSL compiler - tagged on Jun 14, 2015

-   supports a fair amount of Haskell98 language features
-   partially supports GADTs and type families
-   supports explicit type application
-   supports row polymorphism and swizzling
-   uses compositional typing for better error messages
-   OpenGL API provided in attached Builtins and Prelude modules
-   generates LambdaCube3D IR (intermediate representation)


