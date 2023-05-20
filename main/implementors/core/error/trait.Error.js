(function() {var implementors = {
"budlang":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"enum\" href=\"budlang/ast/enum.CompilationError.html\" title=\"enum budlang::ast::CompilationError\">CompilationError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"enum\" href=\"budlang/parser/enum.ParseError.html\" title=\"enum budlang::parser::ParseError\">ParseError</a>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"enum\" href=\"budlang/enum.Error.html\" title=\"enum budlang::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where\n    Env: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> + <a class=\"trait\" href=\"budlang/trait.Environment.html\" title=\"trait budlang::Environment\">Environment</a>,\n    ReturnType: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,</span>"]],
"budvm":[["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"enum\" href=\"budvm/enum.Error.html\" title=\"enum budvm::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where\n    Env: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> + <a class=\"trait\" href=\"budvm/trait.Environment.html\" title=\"trait budvm::Environment\">Environment</a>,\n    ReturnType: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,</span>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"struct\" href=\"budvm/struct.Fault.html\" title=\"struct budvm::Fault\">Fault</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where\n    Env: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> + <a class=\"trait\" href=\"budvm/trait.Environment.html\" title=\"trait budvm::Environment\">Environment</a>,\n    ReturnType: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>,</span>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"enum\" href=\"budvm/enum.FaultKind.html\" title=\"enum budvm::FaultKind\">FaultKind</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"enum\" href=\"budvm/ir/enum.LinkError.html\" title=\"enum budvm::ir::LinkError\">LinkError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"enum\" href=\"budvm/ir/asm/enum.AsmError.html\" title=\"enum budvm::ir::asm::AsmError\">AsmError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"enum\" href=\"budvm/lexer_util/enum.DecodeStringError.html\" title=\"enum budvm::lexer_util::DecodeStringError\">DecodeStringError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.69.0/core/error/trait.Error.html\" title=\"trait core::error::Error\">Error</a> for <a class=\"enum\" href=\"budvm/lexer_util/enum.DecodeNumericError.html\" title=\"enum budvm::lexer_util::DecodeNumericError\">DecodeNumericError</a>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()