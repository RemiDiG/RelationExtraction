From Stdlib Require FunInd Extraction.
Declare ML Module "relation_extraction.plugin".

Parameter generic_eq_bool : forall A, A -> A -> bool.
Register generic_eq_bool as plugins.relation_extraction.generic_eq_bool.
Extract Inlined Constant generic_eq_bool => "(=)".
