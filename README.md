Work in progress for automation tools for spec testing. 

Files:

* mutationEx.dfy : example for mutation testing prototype
* specMutationTest.s.dfy : example of manual muation testing. 
* template.s.dfy : Examples for ND testing 
* specTest.s.dfy : More manual tests 

See `/.scripts` for more details about Fuzzing and Non-Deterministic Testing

---

### Mutation Testing Prototype

Starting with a Spec, and a proof that passes, running a mutating the spec and retrying the proof gives an indication that the spec could be too weak. If a stronger mutated spec still allows the proof to go through, this is a red flag, that the original spec may not be the intended spec. 

https://github.com/eligoldweber/dafny-holeEval/tree/mutations

This is a fork from https://github.com/GLaDOS-Michigan/dafny-holeEval. 

To build:

`make exe`

>Might need to use makefile to install z3 to make sure that it is located in the correct location

To run: 

```
./Binaries/Dafny /rlimit:1000 /compile:0 /allowGlobals /noNLarith /autoTriggers:1 /verifyAllModules /holeEval:[MODULE_NAME].[PREDICATE NAME] /holeEvalRunOnce /holeEvalServerIpPortList:ipPortListOneNode.txt [PATH TO FILE].dfy &> output.txt
```

See `mutationEx.dfy` for example files;

The current prototype will automatically generate the `isStronger` lemma, and the `base` predicate. There is an option to also
generate the `isSame` lemma. To do so uncomment line 901-902 in `Source/Dafny/HoleEvaluator.cs`and rebuilding.

>NOTE: examples of the `isSame` lemma are left commented out in `mutationEx.dfy`

The output from this tool will generate a log in `output.txt` and will display all the attempted mutations, and the ones that passed. As well
as a directory of intermediary files. 

The `isStronger` lemma checks to see if the mutated predicate is stronger than the original predicate. We dont care about weaker mutations. 
It is possible for a mutation to be exactly the same as the original predicate, which will lead to a false positive. The same predicate will also
allow the proof to pass. Avoid this by checking which of the mutations are equal. A TODO is to check this programatically so to only run the proof with
the mutations that are valid. unique and stronger. 


>NOTE: an example for the body of the ipPortListOneNode.txt file is `[IP]:50051` for running both the holeEval tool and the grpc server on the same host. The default port configured for the dafny-grpc-server is 50051. Both the dafny server and holeEval tool can be run on the same machine, but it is suggested to at least use multiple sessions. 

https://github.com/arminvakil/dafny-grpc-server

or building the dafny-grpc-server, you can use the following command:

`bazel-4.0.0 build --cxxopt="-g" --cxxopt="--std=c++17" //src:server`

>Make sure to use bazel version 4.0.0

and for running the grpc-server, you can use the following command:

`./bazel-bin/src/server -d [PATH_TO_DAFNY_BINARY]`

for instance:

`./bazel-bin/src/server -d /proj/vm-vm-PG0/BASE-DIRECTORY/dafny-holeEval/Binaries/Dafny`
