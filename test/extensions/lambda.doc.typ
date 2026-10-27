// Input to `ott -typst_filter`: #text(fill: red, $mono("<<no parses (char 2):  .***..  >>")$) quotations are replaced by
// Typst math for the parsed term.  Compile doc.typ, not this file.
#import "lambda.typ": *

= Call-by-value lambda calculus

Reduction is written $t_1 --> t_2$ and defined by:

#ottdefnreduce()

For example, $ottsym("(")  lambda  italic("x")  ottsym(".")  ottnt("t"_(1))  ottsym(")") thin ottnt("v"_(2))$ reduces to $ottsym("{")  ottnt("v"_(2))  ottsym("/")  italic("x")  ottsym("}")  ottnt("t"_(1))$.

#ottgrammar
