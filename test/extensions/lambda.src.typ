// Input to `ott -typst_filter`: [[ ... ]] quotations are replaced by
// Typst math for the parsed term.  Compile doc.typ, not this file.
#import "lambda.typ": *

= Call-by-value lambda calculus

Reduction is written $t_1 --> t_2$ and defined by:

#ottdefnreduce()

For example, $[[ (\x.t1) v2 ]]$ reduces to $[[ {v2/x}t1 ]]$.

#ottgrammar
