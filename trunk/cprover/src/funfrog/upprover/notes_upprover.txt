Notes regarding development of UpProver Algorithm
>>Indirect interface change:
If a function contains global var and in the 2nd version the global var gets changed, in the diff_checker the function should be marked
as interface-change; For now this issue is handled in summary-validation() with try-catch so that we invalidate the summary
(remove from summary store; remove used_sumaries from node, and set_inlne)
This problem happened in 008.493977f.32_7a.cil_safe.i and 009.64f9477.32_7a.cil_safe.i  from regression_verification benchmarks (Dirk Beyer's benchmarks)