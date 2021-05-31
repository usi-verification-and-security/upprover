# Demo for HiFrog and UpProver

First, please download the demo examples of HiFrog and UpProver from [here](http://verify.inf.usi.ch/sites/default/files/executable/lab_hifrog_upprover.gz) or by running the following command in your machine:

`wget -q http://verify.inf.usi.ch/sites/default/files/executable/lab_hifrog_upprover.gz ;  tar -xzvf  lab_hifrog_upprover.gz`

# Part 1: HiFrog Demo: 
` cd lab_hifrog_upprover/hifrogDemo` navigates to the directory that contains demo examples for HiFrog.

### How to run HiFrog?
```
rm __summaries
hifrog [options] --logic <logic>  <file> --claim <N>
```
where `<logic>` could be `qfuf`, `qflra`, `prop`


### Use of Function Summarization in verifying different assertions: 
- A toy example:

```
rm __summaries
hifrog --logic qflra ex1_lra.c --claim 1 --save-summaries __summaries 
hifrog --logic qflra ex1_lra.c --claim 3 --load-summaries __summaries 
```

- A real benchmark (from industrial sources):

```
hifrog  disk.c --show-claims
```
*Exercise) In program disk.c, record the verification time for reasoning on --claim 79 (i) with using function summaries of claim 1 and (ii) without using function summaries of claim 1*

Hints: 
```
rm __summaries
hifrog --logic qflra  disk.c --claim 1 --save-summaries __summaries 
hifrog --logic qflra  disk.c --claim 79 --load-summaries __summaries 
```
For comparison, remove __summaries then run claim 79.



### Use of Uninterpreted Functions (qfuf) vs. Propositional Logic (prop): 

- Run with propositional logic:
```
rm __summaries
hifrog --logic prop ex_product.c 
```
Too costly! You may need to kill the process manually!

- Run with qfuf logic:
```
rm __summaries
hifrog --logic qfuf ex_product.c
```


### Use of Linear Real Arithmetic (qflra) vs. Uninterpreted Functions (qfuf): 

- Run with qfuf logic:
```
rm __summaries
hifrog --logic qfuf ex_choice.c   
```
Note to the "Warning" the tool reports! It says the reported bug might be due to the abstraction, try with a more precise encoding to make sure!

- Run with qflra logic:
```
rm __summaries
hifrog --logic qflra ex_choice.c 
```



### Summary and Theory Refinement

First see how tedious might be finding an approporiate precision **manually** for each claim! Among qfuf (the cheapest), qflra, prop (the most expensive) encodings, let's find the lightest possible (i.e., less expensive) encoding for verifying each claim of program `sumtheoref2.c`

By running manually for each claim: 
```
rm __summaries
hifrog --logic <logic> sumtheoref2.c --claim <N> --save-summaries __summaries 
```
We trust the safe result (if the over-approximative theory is safe, more precise theories also will be safe), but we don't trust the unsafe result (it might be false positive due to abstracton) unless prop approves it!

Now, run HiFrog with `--sum-theoref` option to see the tool **automatically** will find the appropriate encoding for each claim:
```
hifrog --sum-theoref sumtheoref2.c
```

Solution:
- claim 1: safe by UF
- CLaim 2: safe by LRA (verifiable by LRA solver with adjusted adapted UF summaries)
- Claim 3: safe by UF
- Claim 4: safe by LRA
- Claim 5: safe by PROP 



Exercise) Rune sumtheoref1.c with `--sum-theoref`
```
hifrog --sum-theoref sumtheoref1.c
```

Solution:
- claim 1: safe by UF
- CLaim 2: safe EUF
- Claim 3: unsafe by Prop (counter-example must be approved by Prop)




### Removing redundant assertions:
HiFrog has an option --claims-opt <steps> which identifies and reports the redundant assertions using the threshold <steps> as the maximum number of SSA steps between the assertions including the SSA steps at the functions calls (if any) between the assertions.
```
rm __summaries
hifrog --logic qflra --claims-opt 20 ex_redundant.c
```
  
  

### Error trace:
Whenever a safety property is violated, HiFrog prints a concrete counterexample mapping it to the exact lines in the program: 
```
hifrog  --logic qflra --claim 1 ex_unsafe.c
```
  


  
### User-Provided Summaries:

```
hifrog --logic qflra --list-templates sin_cos.c
```
Edit the summary of the nonlinear function and store it in file `__summaries_nonlin` and  then link it to the verification of  sin_cos.c by running: 
  
```
hifrog --logic qflra sin_cos.c --load-summaries __summaries_nonlin
```

*Exercise) verify the program `mod_mult.c` with Prop, 2) How about with EUF?
3) Generate a summary template with qflra and edit it based on your knowledge, then reuse it with LRA encoding*

See the summary of `mod_mult` function stored in `summaries_mult_mod`



### Tuning the strength of summaries
- LRA strong summary
```
hifrog --logic qflra --claim 1 --itp-lra-algorithm 0 --verbose-solver 2 --save-summaries strong-summary-lra ex_abs.c
```


`(or (<= 0 |abs::#return_value!0#1|) (not (<= 0 (* (- 1) |abs::#return_value!0#1|))))`

  
- LRA weak summary
```
hifrog --logic qflra --claim 1 --itp-lra-algorithm 2 --verbose-solver 2 --save-summaries weak-summary-lra ex_abs.c
```

`(<= (- 2) |abs::#return_value!0#1|)`

      

### Proof reduction
See proof compression information 
```
hifrog --verbose-solver 1 --reduce-proof --logic qfuf --itp-uf-algorithm 0 --claim 1 --save-summaries strong-summary-uf ex_equality.c
```




# Part 2: UpProver Demo: 
` cd lab_hifrog_upprover/upproverDemo` navigates to the directory that contains demo examples for UpProver.

### How to run UpProver
- bootstrapping of the first version
```
rm __summaries
upprover [options] --logic <logic>  <file1> --bootstrapping
```

- summary-validation of the second version
 ```
upprover [options] --logic <logic>  <file1> --summary-validation <file2> 
```


- A toy example

```
rm __summaries __omega
upprover --logic qflra  version1.c --bootstrapping
upprover  --logic qflra  version1.c --summary-validation version2.c 
```

- A real example (Linux kernel device drivers from svcomp20)
```
rm __*
upprover --logic qflra  --unwind 4 --bootstrapping  drivers_video_v1.i 
upprover --logic qflra --unwind 4 drivers_video_v1.i --summary-validation drivers_video_v2.i
```


- Identical code: (Syntactically or semantically identical w.r.t to the property) 
```
rm __*
upprover --logic qfuf --unwind 4 --bootstrapping gpu_v1.i
upprover --logic qfuf --unwind 4  gpu_v1.i --summary-validation gpu_v2.i
```
*Exercise) Verify gpu_v2.i from scratch and compare the runtime with the above incremental check!*



- Other types of changes: 

    1) deleting a function in the new version:
    ```
    upprover --logic qflra ex6-v1.c  --bootstrapping
    upprover --logic qflra ex6-v1.c --summary-validation ex6-v2-delete.c 
    ``` 
  UpProver reprts the assertion has been violated thus a bug is introduced in the 2nd version!
  
    2) changing the signature of functions in the new version:
    ```
    upprover --logic qfuf --bootstrapping ex5_orig.c
    upprover --logic qfuf  ex5_orig.c --summary-validation ex5_signature_chng.c
    ```
    3) introducing a new function to the new version
    

    *Exercise) introduce a new function to ex5_orig.c and verify it!*




- Checking "Tree interpolation property" in generated summaries

```
upprover --logic qflra ex_conj_itp_v1.c --bootstrapping
upprover --logic qflra ex_conj_itp_v1.c --TIP-check
```


- UF vs PROP encoding
```
upprover --logic prop --bootstrapping ex5_orig.c
```
Most likely bootstrapping run will timed out with prop and thus no possibility for incremental check of new versions.
However we can run it with qfuf or qflra!





