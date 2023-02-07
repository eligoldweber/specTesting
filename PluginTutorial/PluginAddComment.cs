using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace PluginAddComment;

public class TestConfiguration : PluginConfiguration {
  public override DafnyCodeActionProvider[] GetDafnyCodeActionProviders() {
    // return new DafnyCodeActionProvider[] { new AddCommentDafnyCodeActionProvider() };
    return new DafnyCodeActionProvider[] { new AddNDLemmaCodeActionProvider() };
  }
}

// public class AddCommentDafnyCodeActionProvider : DafnyCodeActionProvider {
//   public override IEnumerable<DafnyCodeAction> GetDafnyCodeActions(IDafnyCodeActionInput input, Range selection) {
//     var firstTokenRange = input.Program?.GetFirstTopLevelToken()?.GetLspRange();
//     if(firstTokenRange != null && firstTokenRange.Start.Line == selection.Start.Line) {
//       return new DafnyCodeAction[] {
//         new InstantDafnyCodeAction("Insert comment", new DafnyCodeActionEdit[] {
//         new DafnyCodeActionEdit(firstTokenRange.GetStartRange(), "/*First comment*/")
//     })
//   };
//     } else {
//       return new DafnyCodeAction[] { 
//         new CustomDafnyCodeAction(firstTokenRange) 
//       };
//     }
//   }
// }
// public class test : Rewriter
// {
//   public override Get
// }

public class AddNDLemmaCodeActionProvider : DafnyCodeActionProvider {
    private string GetFullName(Microsoft.Dafny.Declaration decl) {
    if (decl is MemberDecl m) {
      return m.FullDafnyName;
    } else if (decl is ModuleDecl mod) {
      return mod.FullDafnyName;
    } else if (decl is TopLevelDecl tld) {
      return tld.FullDafnyName;
    } else {
      return decl.Name;
    }
  }

  public override IEnumerable<DafnyCodeAction> GetDafnyCodeActions(IDafnyCodeActionInput input, Range selection) {
    var firstTokenRange = input.Program?.GetFirstTopLevelToken()?.GetLspRange();
    if(firstTokenRange != null && firstTokenRange.Start.Line == selection.Start.Line) {
      string listOfNames = "";
        foreach (var moduleDefinition in input.Program.Modules()) {
          foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
            if (topLevelDecl is TopLevelDeclWithMembers cd) {
              foreach (var member in cd.Members) {
                  if(member is Predicate){
                      var pred = (Predicate)member;
                      var test = "";
                      Visitor v = new Visitor();
                      // v.Visit(pred.Req);
                      v.Visit(pred);
                      // foreach(var r in pred.Req){
                      //     test = test + " :: " + r as String;
                      // }
                      test = v.path;
                      test = test + "\ncount = " + pred.Formals.Count();
                      foreach (var tp in pred.TypeArgs)
                      {
                        test = test + "\n + :: type -= " + Microsoft.Dafny.Printer.TypeParamString(tp);
                      }
                      // test = test + "\n + :: " + pred.TypeArgs;
                      
                      listOfNames = listOfNames + " :: " + GetFullName(member) + "( " + "Predicate " + test+" )\n";
                  }else{
                    listOfNames = listOfNames + " :: " + GetFullName(member) + "( " + "" + " )\n";
                  }
                  
              }
            }

        }
      }
      var startLoc = firstTokenRange.GetStartRange();
      startLoc = new Range(new Position(0,0),new Position(0,0));
      return new DafnyCodeAction[] {
        new InstantDafnyCodeAction("Insert NP Test", new DafnyCodeActionEdit[] {
        new DafnyCodeActionEdit(startLoc, 
        "/*First comment Test \n" 
        + input.Program?.GetFirstTopLevelToken()?.GetLspRange() + 
        "\n" +
       listOfNames +"\n*/\n")
    })
  };
    } else {
      return new DafnyCodeAction[] { 
        // new CustomDafnyCodeAction(firstTokenRange) 
      };
    }
  }
}


public class CustomDafnyCodeAction: DafnyCodeAction {
  public Range whereToInsert;
        String test = "";
  
  public CustomDafnyCodeAction(Range whereToInsert): base("Insert comment") {
    this.whereToInsert = whereToInsert;
  }
  public override DafnyCodeActionEdit[] GetEdits() {
    return new DafnyCodeActionEdit[] {
      new DafnyCodeActionEdit(whereToInsert.GetStartRange(), "/*A comment*/")
    };
  }
}

  class Visitor : BottomUpVisitor {
    //  private readonly DafnyInfo info;
    public string path;
    // public Printer p;
    public Visitor() {
        // this.info = info;
        path = "";
        // p = new Printer();
      }
    protected override void VisitOneExpr(Expression expr) {
      // if(expr is BinaryExpr){
      path = path + " :: " + Microsoft.Dafny.Printer.ExtendedExprToString(expr) + " \n -- " + expr;
      // }
    }
  }


// using Microsoft.Dafny;
// using Microsoft.Dafny.Plugins;
// using System.Collections;

// namespace PluginsAdvancedTest {

//   /// <summary>
//   ///  Small plugin that detects all extern methods and verifies that there are test methods that actually invoke them.
//   /// </summary>
//   public class TestConfiguration : PluginConfiguration {
//     public string PluginUser = "";
//     public bool ForceName = false;
//     public override void ParseArguments(string[] args) {
//       ForceName = args.Length > 0 && args[0] == "force";
//       PluginUser = args.Length > 1 ? ", " + args[1] : "";
//     }
//     public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
//       return new Rewriter[] { new ExternCheckRewriter(errorReporter, this) };
//     }
//   }

//   public class ExternCheckRewriter : Rewriter {
//     private readonly TestConfiguration configuration;

//     public ExternCheckRewriter(ErrorReporter reporter, TestConfiguration configuration) : base(reporter) {
//       this.configuration = configuration;
//     }

//     public override void PostResolve(Program program) {
//       foreach (var moduleDefinition in program.Modules()) {
//         foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
//           if (topLevelDecl is ClassDecl cd) {
//             foreach (var member in cd.Members) {
//               if (member is Method methodExtern) {
//                 if (Attributes.Contains(member.Attributes, "extern")) {
//                   // Verify that there exists a test method which references this extern method.
//                   var tested = false;
//                   Method candidate = null;
//                   foreach (var member2 in cd.Members) {
//                     if (member2 == member || !(member2 is Method methodTest)) {
//                       continue;
//                     }
//                     if (!Attributes.Contains(methodTest.Attributes, "test")) {
//                       continue;
//                     }
//                     if (!moduleDefinition.CallGraph.Reaches(methodTest, methodExtern)) {
//                       continue;
//                     }
//                     candidate = methodTest;

//                     if (configuration.ForceName && candidate.Name != methodExtern.Name + "_test") {
//                       continue;
//                     }
//                     tested = true;
//                     break;
//                   }

//                   if (!tested) {
//                     var forceMessage = configuration.ForceName ? $" named {methodExtern.Name}_test" : "";
//                     var token = configuration.ForceName && candidate != null
//                       ? new NestedToken(methodExtern.tok, candidate.tok, "You might want to just rename this method")
//                       : methodExtern.tok;
//                     Reporter.Error(MessageSource.Resolver, token,
//                       $"Please declare a method {{:test}}{forceMessage} that will call {methodExtern.Name}{configuration.PluginUser}");
//                   }
//                 }
//               }
//             }
//           }
//         }
//       }
//     }
//   }

// }
