# Artifact: Specification and Verification of Strong Timing Isolation of Hardware Enclaves

The artifact contains the source code for the case studies and Coq-SMT toolchain presented in _Specification and Verification of Strong Timing Isolation of Hardware Enclaves_.

## [Functional] Getting Started (Kick-the-Tires) [10 minutes]

We provide two ways to evaluate our artifact:
* Docker (recommended): a Docker image with dependencies pre-installed and code pre-built.
* From source: see "Getting started" in ``main/README.rst``.

### Install Docker; import and start the image [Docker only]
* Install Docker as described in [https://docs.docker.com/engine/install/](https://docs.docker.com/engine/install/).
* Download the docker image on Zenodo and load it (this may take ~3 minutes):
``` 
docker load --input ccs24_isolation.tar.gz
```
* Run the image:
```
docker run -it ccs24-isolation
```

All code and scripts are in `~/ccs24-isolation` in the Docker image. 

### Install dependencies and compile Coq files [from-source only]
Please see "Getting started" in ``main/README.rst``. After installing dependencies, expect building from source to take ~60 minutes.

### Browse a file in your IDE [Docker & from-source]
Check that you can browse a file (and optionally, interactively step through Coq code) in your IDE.

The following instructions are for Emacs + Proof General and allow you to interactively step through Coq code, but you can also just browse the source files using your favorite editor (e.g. `vim`, or feel free to install another using `apt-get`). Interactively stepping through code is helpful but not mandatory to evaluate this artifact.
* Use a full-screen terminal window.
* Run `emacs main/dkoika/deps/koika/examples/rv_isolation/Machine.v` to open the top-level machine in the case study.
* [Navigate](https://www.gnu.org/software/emacs/tour/) to the end of the file just before `End Machine` and process the Coq source up to that point (`C-c C-enter`). You should see the source window on the left, and two windows named `goals` and `response` on the right. Use `C-c arrowkey` to move the cursor between different emacs windows (from the source to the goal window and back).
* Printing out a definition: navigate your cursor to `Core.schedule` in `Definition lifted_core0_schedule`, and print out the definition of `Core.schedule` using the following four-key sequence: ``C-c C-a C-p enter``. You should see 
```
Core.schedule = Writeback |> Execute |> StepMultiplier |> Decode |> WaitImem |> Fetch |> Tick |> Init |> Purge |> done : scheduler
```
 in the response window. Note that the definition must have been processed in the previous step to be "in scope". 
* Locating a definition: keeping your cursor on `Core.schedule`, show where it is defined using `C-c C-a C-l enter`. You should see ``Constant rv_isolation.RVCore.Core.schedule`` in the response pane.
* Opening a file: `C-x C-f` will display ``Find file: ~ccs24-artifact/main/dkoika/deps/koika/examples/rv_isolation/`` in the bottom status bar. Enter `RVCore.v` to open the processor file.
* Searching: `C-s` will display `I-search` in the bottom status bar. Type `schedule`. Press `C-s`/`C-r` to go to the next/previous occurrence. Find `Definition schedule` and check that it indeed is defined as `Writeback |> Execute |> ...`.
* Exit emacs: `Ctrl-x Ctrl-c`. 
    * Type `yes` if prompted with `Active processes exist; kill them and exit anyway? (yes or no)` (let's disable this in the next step!)

### Optional: customizing emacs, exiting and restarting Docker [Docker only]
While evaluating the artifact, you might want to exit and restart the container, persisting changes.
* Let's make some changes. Add the following lines to ``~/.emacs``:
```
;; disables confirming about active processes when exiting 
(setq-default confirm-kill-processes nil)
;; add mouse support 
(xterm-mouse-mode 1)
```
* Stop the container and exit: 
```
> exit
```
* Find the container's name from the list of stopped containers:
```
> docker ps -a
```
* Restart the container:
```
> docker restart <container-name/id>
> docker attach <container-name/id>
```
* Check any changes you made are still there!

Note: to load the artifact from a _fresh_ state, use ``docker run -it ccs24-isolation``.

## Overview

The artifact contains four branches of the project's github repo, to be released and open-sourced.
1. The primary directory is ``main/`` (please see ``main/README.rst``). The bulk of the evaluation will be here. 
2. ``branch-predictor/`` contains the branch predictor modification (of section 7.1 of the paper). The modified files are ``dkoika/deps/koika/examples/rv_isolation/{Bht.v,Btb.v,RVCore.v}``. The spec and proofs are unchanged.
3. ``enclave-monolithic/`` contains the branch for the monolithic enclave proof, used to obtain numbers for Figure 10. It is largely the same as the modular proof in ``main/``, except that simulation between the implementation and spec machines is checked using one call to the SMT solver (rather than separate calls for the cores, SM, and memory subsystem).
4. ``resource-isolation/`` contains the spec, implementation, and proof of the toy resource isolation example from section 4.1. 

The ``main/`` directory is organized as follows (detailed later in this README, and also described in ``main/README.rst``).
* ``dkoika/deps/koika``: The examples in the paper are written on top of the reference implementation of [Koika](https://github.com/mit-plv/koika/tree/asplos2021) (apart from the resource isolation example, which is written directly in our derivative of Koika, dKoika). See ``main/dkoika/deps/koika/README.rst`` for details about Koika, its reference implementation, verified compiler, and C++ simulator [Cuttlesim](https://dl.acm.org/doi/10.1145/3445814.3446720).
* ``dkoika/src/koika``: This contains our derivative of Koika (referred to as dKoika in the paper), along with static analysis tooling and a symbolic assertion language for our Koika-SMT toolchain.
* ``dkoika/deps/koika/examples/{rv_isolation,rv_cache_isolation}``: the implementation of our case-study machine, with the cache extension in `rv_cache_isolation`.
* ``dkoika/src/koikaExamples/{Enclaves,EnclaveWithCache}``: the specifications and proofs of the case studies.
* ``main/smt_koika``: the SMT translation of dKoika

### Paper-section-to-source-file mapping

In the following, section numbers refer to the submission version of the paper.
1. Introduction
2. Background
3. Overview
4. Specifying and Enforcing Isolation
    * 4.1 Toy Example: Resource Isolation. `resource_isolation/coq/examples/`:
        - Specification: `ResourceIsolation_Spec.v`
        - Instantiating the spec: `ResourceIsolation_Proof.v`
    * 4.2 Static Strong Isolation
    * 4.3 Dynamic Enclave Isolation
5. Case Study: Multicore RISC-V Processor. 
    * Enclave programming model
    * 5.1 Specification. `main/dkoika/src/koikaExamples/Enclaves/{Spec,Theorem}.v`
    * 5.2 Implementation. In `main/dkoika/deps/koika/examples`:
        - Processor: `rv_isolation/RVCore.v`
        - Security monitor: `rv_isolation/SecurityMonitor.v`
        - Memory subsystem:
            * round-robin artbiter: `rv_isolation/Memory.v`
            * system with L1 caches: `rv_cache_isolation/Memory.v`
6. Verifying Strong Isolation in Koika
    * 6.1 Proof architecture: In `main/dkoika/src/`:
        - Specification in Gallina: see 5.1
        - Implementation in Koika: see 5.2
        - dKoika: `koika/{Syntax.v,Semantics.v}`
        - Translation from Koika to dKoika: `koikaExamples/KoikaConversion.v` 
        - Modular decomposition/one-component-at-a-time-semantics: `koika/StaticAnalysisCorrect.v:check_modular_conflicts_correct`, `koikaExamples/Enclaves/Modular_PfSim.v`, `koikaExamples/Enclaves/PfDefs.v:impl_interp_modular_schedule`
        - Proving trace equivalence: `main/dkoika/src/koikaExamples/Enclaves/`:
            * Simulation relation: `PfSim.v:Sim`
            * Single-cycle, circuit postcondition: `PfSim.v:SimPost`
            * Reducing strong isolation to single-cycle preservation: `PfSim.v:{step_sim,step_n'_sim,simulation}`
    * 6.2 Instantiating the Specification: `main/dkoika/src/koikaExamples/Enclaves/{Proof,PfSim}.v` 
    * 6.3 Per-Component Security Obligations: In `main/dkoika/src/koikaExamples/Enclaves/`
        - Processor: ``ProofCore_symb.v``
        - Security Monitor: ``SmProofs.v``
        - Memory subsystem: ``MemoryProofs.v``
    * 6.4 Koika-to-SMT toolchain
        - Symbolic language deeply embedded in Coq (Appendix A.2): `main/dkoika/src/koika/{Symbolic,SymbolicInterp}.v`
        - "Chain together the module specifications": `main/dkoika/src/koikaExamples/Enclaves/Modular_PfSim.v`
        - SMT encoding of Koika: `main/smt_koika/src/koika_smt.ml`
7. Evaluation and Discussion:
    * 7.1 Design modifications:
        * Adding a branch predictor:  ``branch-predictor/dkoika/deps/koika/examples/rv_isolation/{RVCore,Bht,Btb}.v``
        * Adding caches: ``main/dkoika/deps/koika/examples/rv_cache_isolation/Memory.v``
    * 7.2 Verification cost: see "reproducing Figure 10" below.
    * 7.3 Running an Application: ``main/dkoika/deps/koika/examples/rv_isolation/tests``
    * 7.4 Extensions and Future Work
8. Related Work
9. Conclusion

## [Reproducible+Reusable] Step-by-step instructions

This artifact provides:
1. (5.2): A case-study prototype with two pipelined RISC-V cores, a security monitor, and a memory subsystem arbitrating access to a single-port BRAM.
2. (5.1, Figure 7, Appendix A.2): A formalisation of strong timing isolation.
3. (6.1): A Coq-SMT toolchain for verifying isolation, with dkoika, a symbolic assertion language, and an SMT encoding of Koika.
4. (6): A machine-checked proof of the case-study prototype, with per-component security obligations.
5. (7.1): An extension of the processor with a branch target buffer, with machine-checked proof of isolation.
6. (7.1): An extension of the memory subsystem with four L1 caches, with machine-checked proof of isolation.
7. (4.1): An implementation, specification, and proof corresponding to the resource isolation example.
8. (7.3): A small example of running code on our enclave machine.
9. (7.2): Scripts to produce Figure 10, counting lines of code for the various examples and time to check the Coq and SMT proofs. NB: the SMT times differ from the submitted version of the paper and will be updated in the camera ready, see [Step 9](#9.-7.2:-producing-figure-10) for details.

The following provides a guide to evaluate and audit each of the points above. Expect Steps 1-8 to take ~10-20 minutes each. Step 9 will take ~3 hours of mostly inactive time, if you elect to rebuild all the code in all the branches. 

### 1. (5.2): Case-study prototype
Check that the prototype corresponds to the case study described in the paper.

The case study is written using the reference implementation of [Koika](https://github.com/mit-plv/koika/tree/asplos2021), a rule-based hardware description language in the style of Bluespec. Rules appear to execute atomically, or one-rule-at-a-time, following a user-provided schedule.

The main case study is in ``main/dkoika/deps/koika/examples/rv_isolation/``. The machine contains two pipelined RISC-V cores, a security monitor, and a memory subsystem arbitrating access to a single-port BRAM.
- ``rv32.v``: The top-level package, with `circuits` generated using Koika's verified compiler and `koika_package` used to generate C++ code. This is extracted in ``rv32i.v`` to OCaml, and then used to generate Verilog or C++ code for simulation with Cuttlesim.
- ``Machine.v``: A machine contains rules from two cores, the SM, and memory. See ``Definition schedule`` at the end of the file.
- ``RVCore.v``: A 4-stage pipelined RISC-V core, with a custom instruction for context switching between enclaves. ``schedule`` (as in the kick-the-tires phase) defines the processor's rules. The primary rules are ``Fetch`` (search for ``Definition fetch``), ``Decode``, ``Execute``, ``Writeback``, and ``Purge``. 
- ``Memory.v``: round-robin memory arbiter, with four pairs of FIFOs per core (`toIMem,toDMem,fromIMem,fromDMem`) and a shared external main memory ``ext_mainmem``. 
- ``SecurityMonitor.v``: implementation of the security monitor, which filters memory requests from the core based on enclave configuration (``sm_filter_reqs``), forwards responses from the memory to core (``sm_forward_resps``), ensures compliant enclave entering and exiting (``sm_enter_enclave`` and ``sm_exit_enclave``), and arbitrates access to the shared MMIO bus (``sm_do_mmio``).

### 2. (5.1, Figure 7, Appendix A.2): Formalisation of strong timing isolation
Read and audit the specification! Check that the specification describes enclaves running in isolation, communicating only via MMIO, and that enclaves are initialised as brand new machines.

The spec is located in the following files found in ``main/dkoika/src/koikaExamples/Enclaves/``:
- ``Spec.v``:  contains the formalisation of strong timing isolation, with excerpts shown in Figure 7 and Appendix A.2. The specification is expressed as a state machine interacting with the external world. ``Context`` variables are parameters, corresponding to existentially-quantified parameters in the paper in ``Spec_sig`` and used to universally quantify over behaviors of the external world in ``WithExternalWorld``.
- ``Theorem.v``: the top-level theorem is ``Secure_t``, trace equivalence of the implementation and specification for an arbitrary number of cycles. It is parameterised over enclave parameters (such as the size and addresses of each enclave region) and existentially-quantified security parameters such as ``local_step_fn0``, which describes the behavior of an isolated machine. This theorem instantiates the spec above, stating that our implementation is secure if it observably behaves the same as the instantiated spec for any behavior of the external world and initial memory state.

### 3. (6.1): Coq-SMT toolchain

The Coq-SMT toolchain has three parts: Koika->dKoika, a symbolic assertion language for dKoika, and an SMT backend for dKoika.

#### Koika->dKoika
dKoika is an alternative implementation of Koika designed for verification and static analysis. It is syntactically and semantically very similar to the reference implementation. We translate our RISC-V examples into dkoika and then use verified static analyses to translate into a modular dkoika semantics. 

``main/dkoika/src/koika/``
  - ``Syntax.v``: Syntax of dKoika.
  - ``Semantics.v``: Semantics of dKoika. Focus on ``interp_action`` and ``interp_cycle``.
``main/dkoika/src/koikaExamples/KoikaConversion.v``: transpiler from Koika to dKoika.

Auditing guide:
1. Check that dKoika's syntax and Koika's syntax (``main/dkoika/deps/koika/coq/Syntax.v``) are similar.
2. Check that dKoika's semantics and Koika's semantics (``main/dkoika/deps/koika/coq/TypedSemantics.v``) are similar.
3. Audit that the translation from Koika to dKoika (``convert``) is sensible for all values that return ``Success``. 

#### Symbolic assertion language
dkoika is accompanied with a symbolic assertion language, used to generate SMT assertions and then reflected back into Coq props for use in proofs. A verified preprocessing step adds typing and debugging annotations for use in SMT.

``dkoika/src/koika/``:
  - ``Symbolic.v``: Symbolic assertion language used for SMT. A ``file_t``, which contains the dkoika machine and pre- and post-conditions, is extracted for SMT-Koika.
  - ``SymbolicInterp.v``: Symbolic assertion language interpretation and helper functions. THe primary functions are `interp_spred` and `interp_spred2`, which reflect the symbolic assertions into Coq propositions, and `symbolic_evaluate_file_success`, which axiomatizes the correctness of the SMT-Koika translation.

#### SMT-Koika
SMT-Koika translates a Koika machine together with symbolic assumptions and assertions into a (single-cycle) SMT query, checked using Z3. The solver returns ``UNSAT :)`` if the assertions hold and ``SAT :(`` if the assertions do not hold, along with a counterexample that the proof developer can query. If the assumptions are false, SMT-Koika will fail with "Assumes are false". 

``main/smt_koika/src/``:
  - ``koika_smt.ml``: SMT translation of Koika.
  - ``query_*``: query language to inspect and debug counterexamples at each rule.

To check an individual file (generated files for the case study are in `main/dkoika/smt_cache/{out_Enclaves,out_EnclaveWithCache}`), run:
```
  > cd main/smt_koika/src
  > ./build_file.sh <your-extracted-file>.ml  # e.g. ../../dkoika/smt_cache/out_Enclaves/Smt_ok_core0.ml
  > ../_build/default/src/main.exe -o debug.txt -q 
```

The optional ``-o`` flag outputs a counterexample (if one is found) along with failed assertions, for debugging. The optional ``-q`` flag provides a query interface for inspecting counterexamples. See [Test the Koika-SMT toolchain can return SAT](#test-the-koika-smt-toolchain-can-return-sat) below.


### 4. (6): Machine-checked proof of the case-study prototype

``main/dkoika/src/koikaExamples/Enclaves``
- ``Proof.v``: proof of the theorem. The ``Print Assumptions`` line at the end prints out all Coq assumptions the proof relies on (i.e. the SMT assertions hold). To check the proof, open ``Proof.v`` in Emacs + Proof General, navigate to `Print Assumptions ConcreteSecure.secure` at the end of the file, and process the Coq buffer to this point (`C-c C-enter`). This will take ~60 seconds. The expected output (ignoring warnings, order may vary) is included below `Print Assumptions`, and is explained as follows:
    * `functional_extensionality_dep`: functional extensionality, a standard assumption in Coq developments.
    * `SymbolicInterp.symbolic_evaluate_success`: axiomatizes the correctness of our (trusted) Koika-SMT translation, for any `WF_single_file` or `WF_product_file`.
    * `SMT_*_ok`: Calls to the SMT solver. We assume in Coq (and should verify below) that the SMT solver returns ``UNSAT :)`` for all these files.

- ``SMT_*.v``: generates files for SMT-Koika.

The SMT assertions can be checked by running the following (allocate ~10 minutes):
```
  > cd main/smt_koika
  > ./scripts/time_smt.sh ../dkoika/smt_cache/out_Enclaves smt_Enclaves
```
This runs all the extracted SMT files in `../dkoika/smt_cache/out_Enclaves`, outputting the results in `smt_Enclaves/`. Ignore terminal output. `cat` an output file ending in `debug.log` to view the rules executed, the result of the SMT query, and the runtime. To view the abbreviated results, run: 
```
    cat smt_Enclaves/*.log
```
The expected output is ``UNSAT :)`` for all files. You should audit that the assumptions in Coq correspond to the SMT solver calls.

### 5. (7.1): Branch predictor extension
``branch-predictor/`` contains the branch predictor modification (of section 7.1 of the paper). The branch predictor and modifications are in ``dkoika/deps/koika/examples/rv_isolation/{Bht.v,Btb.v,RVCore.v}``. In `RVCore.v`, changes are primarily in the `fetch`, `decode`, and `execute` rules.

* ``branch-predictor/dkoika/src/koikaExamples/Enclaves/Proof.v``: Audit the output of `Print Assumptions` as in Step 4.
* Check the SMT output as in Step 4 (~10 minutes):
```
  > cd branch-predictor/smt_koika
  > ./scripts/time_smt.sh ../dkoika/smt_cache/out_Enclaves smt_Enclaves
  > cat smt_Enclaves/*.log
```
* Check that the spec and proofs are unchanged, either via manually auditing or
```
  diff main/dkoika/src/koikaExamples/Enclaves branch-predictor/dkoika/src/koikaExamples/Enclaves
```
Note: ignore changes to `Monolithic_PfSim.v`; it is only used in `enclave-monolithic`.

### 6. (7.1): Cache extension

We implemented a memory subsystem with four L1 caches (two per core, for instruction and data memory) without a cache-coherence protocol. 
* The implementation is in ``main/dkoika/deps/koika/examples/rv_cache_isolation/Memory.v`` (the security monitor and processor are unchanged from the main case study). `do_cache_req` implements the main cache state machine.
* The proof is in ``main/dkoika/src/koikaExamples/EnclaveWithCache``. The invariants for the memory can be examined in `MemoryProofs.v`.
* To audit, check the output of ``Print Assumptions`` in ``Proof.v` as in Steps 4&5, and run the SMT files pertaining to the cache (this will take ~10 minutes):
```
  > cd main/smt_koika
  > ./scripts/time_smt.sh ../dkoika/smt_cache/out_EnclaveWithCacne smt_EnclaveWithCache
  > cat smt_EnclaveWithCache/*.log
```

### 7. (4.1): Resource isolation example
The resource isolation example contains two pairs of F and G boxes. This example was written directly in dKoika using an older version of the library. Nonetheless, the specification style resembles that of the RISC-V prototype.

``resource_isolation/coq/examples/``:
- ``ResourceIsolation_Spec.v``: specification as a state machine interacting with the external world, running jobs in isolation. Note that the spec is parameterised over the local state transition function `local_step_running`, and thus does not constrain the behavior of F and G boxes (in fact, it does not mention F and G boxes).
- ``ResourceIsolation_Theorem.v``: The top-level theorem. Note the existentially-quantified parameters, independence over functional specification of the F and G boxes, and theorem over an arbitrary number of cycles.
- ``ResourceIsolation_Impl.v``: Implementation corresponding to (4.1) with F and G boxes.
- ``ResourceIsolation_Proof.v``: Proof of the theorem. 

To check the proof, open ``ResourceIsolation_Proof.v`` in Emacs + Proof General, navigate to `Print Assumptions Secure.secure` at the end of the file, and process the Coq buffer to this point (`C-c C-enter`). The expected output is as follows, corresponding to assuming functional extensionality (common in Coq developments):
```
Axioms:
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
```
Alternatively, `cat resource_isolation/time_of_build.log` to see the output from the build (grep for "Axioms"), or rebuild the proof completely (see "Producing Figure 10").

### 8. (7.3): Running enclave code
To test the functionality of our prototype, we run some tests using the C++ simulator Cuttlesim (and also Verilator, for the main case study prototype). Note that the prototype is not intended for reuse as-is for building enclaved hardware (and this was not the focus of the paper), and as such we merely run simple tests to validate that the machine can run RISC-V code compiled with gcc and execute an enclave context switching instruction.

In `main/deps/koika/examples/rv_isolation`:
* Run `make cuttlesim-tests` to compile the design for Cuttlesim and run tests in `tests/{riscv_tests,integ}`. An individual test can be run using, e.g.
```
> _objects/rv32i.v/rvcore.cuttlesim.opt tests/_build/rv32i/integ/primes.rv32 <ncycles>
```
`ncycles` specifies the number of cycles the test should be run for. `-1` is interpreted as "run until a finish signal is received".
* Run `make verilator-tests` to compile the design for Verilator and run the tests using Verilator (this will take longer than running with Cuttlesim, e.g. the primes example below will take ~5 minutes).
```
_objects/rv32i.v/obj_dir.opt/Vtop +VMH=tests/_build/rv32i/integ/primes.vmh -1
```
* `tests/enclave` contains simple linker scripts to place enclave code in the appropriate memory regions as well as assembly code to demonstrate enclave context switching functionality (e.g. saving and restoring registers when context switching and supporting function calls with code compiled using `riscv-none-embed-gcc`).
    ** In this example, `enclave0.c` calls the `_add_password` function. In `bootloader0.S`, this calls the custom Enclave switching instruction to switch to Enclave2 with no MMIO permissions, after saving registers on the stack. Enclave2's bootloader inspects the argument register to `call_add_password`, runs the corresponding C function from `enclave2.c`, then clears its registers and returns execution to Enclave0. Enclave0 then calls `_lookup` and a similar process ensues.
``` 
> cd tests/enclave && make && cd ../../
> _objects/rv32i.v/rvcore.cuttlesim.opt tests/enclave/_build/enclave.rv32 -1
```
The expected output is `1->S@*ST` and `PASS`.

### 9. (7.2): Producing Figure 10

Here, we provide instructions to produce Figure 10. 
```
|                | SLOC                               | Time (s)          |
--------------------------------------------------------------------------
| Design         | Koika   Csim   Vlog   Spec     Pf  | Coq      SMT      |
---------------------------------------------------------------------------
| Resource       |   630      -      -    160   6620  |  130      -       |
| Enc:pf-mono    |  2410  12780   1870    280  12550  |  540   720,360,1  |
| Enc:pf-mod     |     "      "      "      "  13080  |  780   200, 95,1  |
| Enc+BTB        |  2750  14760   2160      "  13030  |   "    340,160,1  |
| Enc+Caches     |  2850  17710   2320      "  17750  | 1340   380, 95,1  |
```
Time may vary depending on machine. The table above differs from the submitted version of the paper due to updates in the code from submission, and we will update the text accordingly. Namely:
* The machine resets fewer registers when purging (corresponding to there being many states equivalent to an empty pipeline), weakening the invariant and increasing SMT time for checking (primarily) the processor.
* For the Enc+BTB example, we now also include a BHT. The proof lines differ from Enc:pf-mod due to unrelated reasons (branches of the repository not kept in sync).
* There are some minor variations in the SLOCs due to code updates.

Regarding Coq build times: we provide instructions to recompile just the Coq proofs pertaining to isolation. If you'd like, you can rebuild the entire development including dependencies using ``make clean && make`` in the ``dkoika`` subdirectories (which will take ~45 minutes).

#### Resource [5-10 minutes]
* SLOC: ``cd resource_isolation && ./sloc.sh``. The expected output is 626, 157, and 6621 for the implementation, spec, and proof files respectively. The SLOC in Figure 10 are rounded to the nearest 10 lines of code (e.g. 626 -> 630).
* To rebuild the Coq proofs, in the `resource_isolation` directory, run ``make clean && ./time_build.sh``. This rebuilds dKoika as well. We report the time to compile the code in `coq/examples/*` in Figure 10. In the provided `time-of-build-pretty.log` file, the total time is `131.43 seconds`.

#### Enclave:pf-mono [40 minutes]
* SLOC:
    * Koika, Csim, Vlog: ``cd enclave-monolithic/dkoika/deps/koika/examples/rv_isolation && ./sloc.sh``. 
    ** Spec, Pf: ``cd enclave-monolithic/dkoika/koika/src/koikaExamples/Enclaves && ./sloc.sh``. 
* Time:
    * SMT: 
```
> cd enclave-monolithic/smt_koika 
> ./scripts/time_smt.sh ../dkoika/smt_cache/out_Enclaves smt_Enclaves 
> ./scripts/extract_smt_time.sh smt_Enclaves
```
    * Coq:
```
> cd enclave-monolithic/dkoika && rm -rf _build/default/src/koikaExamples/Enclaves
> time make
```
We report the total time.

#### Enclave:pf-mod [25 minutes]
* SLOC:
    * Koika, Csim, Vlog: ``cd main/dkoika/deps/koika/examples/rv_isolation && ./sloc.sh``.
    * Spec, Pf: ``cd main/dkoika/koika/src/koikaExamples/Enclaves && ./sloc.sh``. 
* Time:
    * SMT: If you ran `time_smt.sh` in Step 4, skip rerunning and just execute `extract_smt_time.sh`.
```
> cd main/smt_koika 
> ./scripts/time_smt.sh ../dkoika/smt_cache/out_Enclaves smt_Enclaves  # skip if done in Step 4
> ./scripts/extract_smt_time.sh smt_Enclaves

```
    * Coq:  
```
> cd main/dkoika && rm -rf _build/default/src/koikaExamples/Enclaves 
> time make
```

#### Enc+BTB [25 minutes]
Same as for [Enclave:pf-mod](enclave:pf-mod-25-minutes), but `s/main/branch-predictor`.

#### Enc+Caches [30 minutes]
Same as for [Enclave:pf-mod](enclave:pf-mod-25-minutes), but `s/Enclaves/EnclaveWithCache`.

## [Reusable] Reusing the artifact for further experiments

This artifact provides and packages the following components that can be used for future work and experiments:
1. A prototype, baseline RISC-V design implementing strong timing isolation.
    * An example of extending the processor in the baseline design with a BTB+BHT
    * An example of extending the memory subsystem in the baseline design with caches
2. An alternative implementation of Koika (dKoika) designed for verification, with a function to convert from the reference implementation to dKoika.
3. A symbolic assertion language for dKoika that reflects back into Coq for use in proofs.
4. An SMT tool to check assertions from the above symbolic assertion language, with a query interface for counterexample inspection and scripting to execute files generated from a Coq build.

Below, we suggest a few starting points for further experimentation.

### Test the Koika-SMT toolchain can return SAT
It's good practice to check that the SMT solver returns SAT when the property being verified is false!

We included an abbreviated version of `ProofCore_Symb.v` in `main/dkoika/src/koikaExamples/Enclaves/CounterexampleDemo.v`. This file attempts to assert that the Core's invariant (``invariant``: certain registers are reset when in a `Purged` state) holds in the post-condition (``post_conds``), without assuming that it holds in the pre-condition (``pre_conds``).

* Open `CounterexampleDemo.v` in emacs+PG.
* Navigate to the end, and process the Coq buffer using `C-c C-enter` to extract the file to OCaml. This will create the file `main/dkoika/src/koikaExamples/Enclaves/TestCounterexample.Test0.ml`.
* Run this using SMT-Koika.
```
  > cd main/smt_koika/src
  > ./build_file.sh `../../dkoika/src/koikaExamples/Enclaves/TestCounterexample.Test0.ml`.
  > ../_build/default/src/main.exe -o debug.txt -q 
```

The expected output is as follows:
```
SMT_FILE
------BEGIN 0 RlCore0_Writeback-----
------BEGIN 1 RlCore0_Execute-----
------BEGIN 2 RlCore0_StepMultiplier-----
------BEGIN 3 RlCore0_Decode-----
------BEGIN 4 RlCore0_WaitImem-----
------BEGIN 5 RlCore0_Fetch-----
------BEGIN 6 RlCore0_Tick-----
------BEGIN 7 RlCore0_Init-----
------BEGIN 8 RlCore0_Purge-----
ADDING_ASSUMPTIONS
Checkpoint passed: assumes are SAT
ADDING_ASSERTIONS
SAT :(
Enter query or STOP: 
```

``SAT :(`` indicates a counterexample was found, outputted in `debug.txt`. A model is printed at the start of `debug.txt`. Then, each of the assertions are evaluated (grep for `EVALUATING ASSERTIONS`, or `false: ` to find an assertion that does not hold).

For example (counterexample found may differ), we found:
```
false: (= |__init{Extracted.MachineImpl}[("Core0_core_id", 90)]@R9| #b0)
```
This corresponds to the `CoreIdSame` assertion, assertion that the register "Core0_core_id" (with ID 90) is not equal to 0 after executing 9 rules.
We can query ``RI 90 @ 9 `` to evaluate the counterexample for "Core0_core_id" after 9 rules, obtaining output ``("Core0_core_id", 90):#b1`` (it is equal to 1).

Here are some other example queries:
* ``RIS (0,10) @ 0``: output registers with ids from 0 to 10 before executing any rules.
* ``RIS [1,3,5] @ 3``: output registers with ids 1,3, and 5 after executing 3 rules.
* (Not applicable for this example): for SMT queries with a product machine (impl+spec), `RS` and `RSS` prints out registers in the spec machine.
 
### Run code on the baseline machine
Write and run your own tests in ``main/dkoika/deps/koika/examples/rv_isolation/tests``! 

Following the steps from [Step 8](8.-7.3:-running-enclave-code), add some RISC-V or C code and compile using `make`. The designs can be debugged using `gdb`, following the [Cuttlesim guide](https://github.com/mit-plv/koika/tree/asplos2021/etc/ae).

### Modify the baseline machine
We provided an example of modifying the processor with a BTB+BHT and memory subsystem with caches. Feel free to add your own modifications. For example:
* Add a custom RISC-V instruction.
* Modify the branch prediction scheme.
* Try breaking the design: disable the security monitor's filtering of memory requests or arbitration to the MMIO, rebuild the proofs and rerun the SMT queries.

### Modify the per-component security obligations

``ProofCore_Symb.v``, ``SmProofs.v``, and ``MemoryProofs.v`` contain per-component security obligations for the processor, security monitor, and memory respectively. These assertions are extracted to OCaml in the ``SMT_*.v`` files in the final build, but for debugging we generate them interactively using emacs+PG.
* Grep around for "Extraction" in these files, and uncomment out test code that generates SMT assertions without rebuilding the entire development.
* Modify/remove/add some assertions (potentially after modifying the design!), then process the Coq buffer to the "Extraction" command to output a file for SMT-Koika as in
    [the CounterexampleDemo experiment](test-the-koika-smt-toolchain-can-return-sat).
* Run the file using [SMT-Koika](smt-koika).

### Write your own new design!
You can also write a new Koika design and do some assertion-based testing, without proving strong timing isolation!
* Write a simple design in Koika, see [Koika's README](https://github.com/mit-plv/koika) and optionally test it using Cuttlesim/Verilator.
* Translate to dkoika using `KoikaConversion.v`, as in ``main/dkoika/src/koikaExamples/Enclaves/Impl.v``
* Write some assertions on the design, as in ``ProofCore_Symb.v``, ``SmProofs.v``, and ``MemoryProofs.v``.
* Extract to OCaml, and run it using SMT-Koika as in the previous section.

### Recipe for formalising and proving strong timing isolation
1.  Write a spatially and temporally partitioned implementation with observation function, in an HDL with formal semantics.
2.  Write a specification state machine with observation function, instantiated with spatial partitions of the implementation.
3.  State strong isolation theorem: trace equivalence.
4.  State per-cycle implementation, specification, and simulation invariants and postconditions, decomposed into per-module assertions when convenient. Implementation postconditions may include reaching and maintaining a state functionally equivalent to a new machine when context switching. Specification invariants may include asserting that the enclave machines enforce the enclave programming model. Simulation invariants define equivalence between the implementation and specification.
5.  Prove invariants are preserved and postconditions hold at each cycle, using SMT where possible in an assertion-based verification style.
6.  Prove soundness of the metatheory and reduction to single-cycle verification in Coq, including reasoning about any external models such as memory or MMIO.

