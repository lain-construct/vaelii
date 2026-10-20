# not-under-thing: proposed genl edges

The proposals cover the seven starter terms that kb-integrity reports under `:not-under-thing` in CxWell.
Paths are under `resources/kb/upper/`. Line numbers are at the tip of `lain/starter-integrity`.
The last commit on the branch stages these edges.

| term | proposed genl | reason | sibling evidence |
|---|---|---|---|
| declined_rule_macro | `closed_predication` | Each instance is a suggested declaration, a ground atomic sentence such as `(genl livesIn locatedIn)`. | positiveExampleComment core.txt:1997; closed_predication comment reflection.txt:42; quoted formula argument `(quotedArg argN 3 formula)` core.txt:423 |
| forced_monotonic_predicate | `predicate` | Every roster member is applied in a sentence: the relation marks, the arity classes, genlCx, folk_species, the equality relations and except. | `(genl decontextualized_predicate predicate)` core.txt:823; `(genl forced_decontextualized_predicate predicate)` core.txt:1233; roster members core.txt:1240-1286, organism.txt:137 |
| forced_monotonic_between_predicates | `predicate` | Its one member is genl, and its arg 1 is already `predicate`. | `(arg forced_monotonic_between_predicates 1 predicate)` core.txt:1294; core.txt:823; core.txt:1233 |
| relation_kind | `type` | Its members instance_relation_predicate and type_relation_predicate are first-order types whose instances are binary predicates. | `(genl folk_species type)` organism.txt:130, another disjoint_metatype; `(set/monotonic (type binary_predicate))` core.txt:1640; `(type logical_constant)` core.txt:1566 |
| type_type_by_order | `fixed_order_type` | Its members type, metatype and meta_metatype each hold members of one order. | `(typeGenl type_type_by_order fixed_order_type)` core.txt:2069; members core.txt:2059-2061 |
| stuff_type_by_state_of_matter | `type` | Its members gas, liquid, plasma and solid are first-order types of substance. | `(genl folk_species type)` organism.txt:130; members abstract.txt:520-523 |
| stuff_type_by_substance | `type` | Its members glass_stuff, metal_stuff, stone and wood are first-order types of substance. | `(genl folk_species type)` organism.txt:130; members abstract.txt:524-527 |

## Notes

- forced_monotonic_predicate: `except` carries no type or arity declaration. The edge makes `except` a predicate with no fixed_arity or variable_arity membership. The develop comment at core.txt:1238-1241 gave that as the reason the term declares no arg type. It also named equals and sameAs as having no arity, and both are declared `binary_predicate` (core.txt:1419, 1423). The staged commit rewrites that comment. `nowhere_never`, the genl of relation, is the true parent that leaves except untyped.
- type_type_by_order: `at_least_metatype` is also true of all three members, and neither parent subsumes the other. `at_least_metatype` would add `(at_least_metatype type)`. Then `(predAllSpecified typeGenl at_least_metatype)` (core.txt:2073) would require a typeGenl for `type`, which the starter does not state.
- declined_rule_macro: the starter holds no record, so the edge concludes nothing on a starter load.
