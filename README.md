# low-level-virtual-machine_llvm
this github has patches of llvm framework for optimizing Intermediate representation of code generation of object file . 

CFCSS - control flow graph through software signature
        there may be sometimes illegal branching due to some hardware or software bug during runtime
        assigning signature in each basic block at compile time helps in entering legal basic blocks on 
        branching . These signatures are special numbers generated in software
        
Decreasing Load-Store usage - load-store use memory requirements , instead if we use registers to move intermediate values 
                              significantly improves loop optimiztions , nearly 4 times faster
                              
    
Loop optimizations - in the intermediate representation loops have 3 basic blocks - for initialization , for body , for condition.
                     using Phinode generation we can internally manipulate loop bodies , since phinode is closer to register it is faster
                     and do not use wait for memory transactions . pushing loop conditions and parallel code in phinode optimizes the loop                      almost 3 times
