(function() {var implementors = {};
implementors["budlang"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.64.0/std/error/trait.Error.html\" title=\"trait std::error::Error\">Error</a> for <a class=\"enum\" href=\"budlang/ast/enum.CompilationError.html\" title=\"enum budlang::ast::CompilationError\">CompilationError</a>","synthetic":false,"types":["budlang::ast::CompilationError"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.64.0/std/error/trait.Error.html\" title=\"trait std::error::Error\">Error</a> for <a class=\"enum\" href=\"budlang/parser/enum.ParseError.html\" title=\"enum budlang::parser::ParseError\">ParseError</a>","synthetic":false,"types":["budlang::parser::ParseError"]},{"text":"impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.64.0/std/error/trait.Error.html\" title=\"trait std::error::Error\">Error</a> for <a class=\"struct\" href=\"budlang/vm/struct.Fault.html\" title=\"struct budlang::vm::Fault\">Fault</a>&lt;'a, Env, ReturnType&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.64.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;ReturnType: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.64.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,&nbsp;</span>","synthetic":false,"types":["budlang::vm::Fault"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.64.0/std/error/trait.Error.html\" title=\"trait std::error::Error\">Error</a> for <a class=\"enum\" href=\"budlang/vm/enum.FaultKind.html\" title=\"enum budlang::vm::FaultKind\">FaultKind</a>","synthetic":false,"types":["budlang::vm::FaultKind"]},{"text":"impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.64.0/std/error/trait.Error.html\" title=\"trait std::error::Error\">Error</a> for <a class=\"enum\" href=\"budlang/enum.Error.html\" title=\"enum budlang::Error\">Error</a>&lt;'a, Env, ReturnType&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.64.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;ReturnType: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.64.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,&nbsp;</span>","synthetic":false,"types":["budlang::Error"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()