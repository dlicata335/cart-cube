
# Cartesian Cubical Type Theory 
by Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, 
Kuen-Bang Hou (Favonia), Robert Harper, Daniel R. Licata
```
  cart-cube.pdf -- draft paper
  cart-cube-original.pdf -- orignal version of paper
                            (with a different composition for Glue types)
  agda/ -- Agda formalization
           (compile ABCFHL.agda to check everything)
```

# A Model of Type Theory with Directed Univalence in Bicubical Sets
by Matthew Z. Weaver and Daniel R. Licata

```
  agda/directed/ -- Agda formalization
                    (compile All.agda to check everything)
```

Both Agda formalizations use an experimental branch of Agda called
agda-flat (version 2.6.0.1), which can be installed by
```
  git clone https://github.com/agda/agda
  cd agda
  git checkout flat
  cabal update
  cabal install --program-suffix=-flat
```
This will create an executable named agda-flat that you can use at the
command line or through the Agda emacs mode (add -flat to agda and
agda-mode in your .emacs).  


