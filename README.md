Work in progress for automation tools for spec testing. 

Files:

* maxPredMutation.dfy : example for mutation testing prototype (incorrect Spec)
* correctMaxPredMutation.dfy : example for mutation testing prototype (correct Spec)
* kvEx.dfy : Key Value refinement proof
* specMutationTest.s.dfy : example of manual muation testing. 
* template.s.dfy : Examples for Non-Deterministic testing 
* specTest.s.dfy : More manual tests 

See `/.scripts` for more details and documentation about Fuzzing and Non-Deterministic Testing

---

### Mutation Testing Prototype

Starting with a Spec, and a proof that passes, running a mutatation of the spec and having  the proof pass gives an indication that the spec could be too weak. If a non-weaker mutated spec still allows the proof to go through, this is a red flag, that the original spec may not be the intended spec. 

https://github.com/eligoldweber/dafny-holeEval/tree/mutations

This is a fork from https://github.com/GLaDOS-Michigan/dafny-holeEval. 

To build:

`make exe`

>Might need to use makefile to install z3 to make sure that it is located in the correct location

To run: 

```
./Binaries/Dafny /rlimit:1000 /compile:0 /allowGlobals /noNLarith /autoTriggers:1 /verifyAllModules /holeEval:[MODULE_NAME].[PREDICATE NAME] /proofName:[MODULE_NAME].[PREDICATE NAME] /holeEvalRunOnce /holeEvalServerIpPortList:ipPortListOneNode.txt [PATH TO FILE].dfy &> output.txt
```

By including the `/proofName` commandline parameter, this tool will only check the mutated spec with the full proof if it pases some pre-processing steps that determine if the spec is strictly not weaker or eqaul to the original spec.

Include `/proofModuleName` if the proof is containted in a different module. In this case the tool will comment out this entire module when doing pre-processing. This module must be the last module in the file. Additionally, all needed modules (ie. `import opened module`) must be in the same file. 

See `correctMaxPredMutation.dfy`, and `maxPredMutation.dfy` for example files;

for example:

```
./Binaries/Dafny /rlimit:1000 /compile:0  /allowGlobals /noNLarith /autoTriggers:1 /verifyAllModules /holeEval:maxExample.maxSpec /proofName:maxExample.max /holeEvalRunOnce /holeEvalServerIpPortList:ipPortListOneNode.txt ~/maxPredMutation.dfy &> output.txt
```

KV mutation example: 

```
./Binaries/Dafny /compile:0 /timeLimit:60 /trace /arith:5 /noCheating:1 /holeEval:MapSpec.QueryOp /proofName:RefinementProof.RefinementNext /proofModuleName:RefinementProof /holeEvalRunOnce /holeEvalServerIpPortList:PortListOneNode.txt ~/counterExampleTest/specTesting/kvEx.dfy &> output.txt
```

The output from this tool will generate a log in `output.txt` and will display all the attempted mutations, and the ones that passed. As well
as a directory of intermediary files. 

There are 2 prepocessing steps `isWeaker` lemma checks to see if the mutated predicate is weaker than the original predicate. We dont care about weaker mutations. 
It is possible for a mutation to be exactly the same as the original predicate, which will lead to a false positive. The next check fixes this by checking which of the mutations are equal. 


>NOTE: an example for the body of the ipPortListOneNode.txt file is just `[IP]:50051` for running both the holeEval tool and the grpc server on the same host. The default port configured for the dafny-grpc-server is 50051. Both the dafny server and holeEval tool can be run on the same machine, but it is suggested to at least use multiple sessions. 

https://github.com/arminvakil/dafny-grpc-server

or building the dafny-grpc-server, you can use the following command:

`bazel-4.0.0 build --cxxopt="-g" --cxxopt="--std=c++17" //src:server`

>Make sure to use bazel version 4.0.0

and for running the grpc-server, you can use the following command:

`./bazel-bin/src/server -d [PATH_TO_DAFNY_BINARY]`

for instance:

`./bazel-bin/src/server -d /proj/vm-vm-PG0/BASE-DIRECTORY/dafny-holeEval/Binaries/Dafny`
