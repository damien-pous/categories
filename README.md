A Rocq library about category theory and monoidal categories

- homepage: https://perso.ens-lyon.fr/damien.pous/string-diagrams/
- string diagram graphical editor: https://github.com/damien-pous/string-diagrams/

# REQUIREMENTS

- rocq-prover >= 9.1
- rocq-partial-orders (https://github.com/damien-pous/partial-orders) 

# AUTHORS

- Damien Pous (CNRS, Plume team, LIP, ENS de Lyon)

Based on work with/of
- Samuel Arsac (ENS de Lyon, Plume team, LIP, ENS de Lyon)        [graph-rewriting library]
- Kazuhiko Sakaguchi (ENS de Lyon, Plume team, LIP, ENS de Lyon)  [rewriting modulo tactics]
- Cyril Cohen (Inria, Cash team, LIP, ENS de Lyon)                [initial template for categories in HB]
- Olivier Laurent (CNRS, Plume team, LIP, ENS de Lyon)            [discussions on monoidal cats]
- Russ Harmer (CNRS, Plume team, LIP, ENS de Lyon)                [discussions on graph-rewriting library]

(cf. https://gitlab.com/SamuelArsac/graph-rewriting , and the category theory example of hierarchy-builder, written by Cyril)

# COMPILING

make

(compilation of theories/monoidal_tactic.v takes long)

# FILES

see file _RocqProject, which is documented
main dependencies are listed below

cat < morphisms < functor < adjunction < (co)limit <
                < bicat   < monoidal <             <
    < (co)span  < (co)product        < cartesian   <
                < pullback/pushout                 <
		                                           < base

in base: 
  all exports 
  + (co)spans as (co)cones
  + products/pullbacks as limits
  + coproducts/pushouts as colimits
  + lifting 0,1,BProd/BCoprod,PB,PO through adjunctions
    thus duality for cartesian cats, 
	thus lifting of coproducts to functors


# LICENSE

GNU LGPL3+

