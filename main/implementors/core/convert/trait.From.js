(function() {var implementors = {
"budlang":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"budlang/ast/struct.Function.html\" title=\"struct budlang::ast::Function\">Function</a>&gt; for <a class=\"enum\" href=\"budlang/ast/enum.Declaration.html\" title=\"enum budlang::ast::Declaration\">Declaration</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"budlang/ast/struct.CodeUnit.html\" title=\"struct budlang::ast::CodeUnit\">CodeUnit</a>&gt; for <a class=\"enum\" href=\"budlang/ast/enum.Declaration.html\" title=\"enum budlang::ast::Declaration\">Declaration</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;LinkError&gt; for <a class=\"enum\" href=\"budlang/ast/enum.CompilationError.html\" title=\"enum budlang::ast::CompilationError\">CompilationError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;DecodeNumericError&gt; for <a class=\"enum\" href=\"budlang/parser/enum.ParseError.html\" title=\"enum budlang::parser::ParseError\">ParseError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;DecodeStringError&gt; for <a class=\"enum\" href=\"budlang/parser/enum.ParseError.html\" title=\"enum budlang::parser::ParseError\">ParseError</a>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"budlang/parser/enum.ParseError.html\" title=\"enum budlang::parser::ParseError\">ParseError</a>&gt; for <a class=\"enum\" href=\"budlang/enum.Error.html\" title=\"enum budlang::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budlang/trait.Environment.html\" title=\"trait budlang::Environment\">Environment</a>,</span>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"budlang/ast/enum.CompilationError.html\" title=\"enum budlang::ast::CompilationError\">CompilationError</a>&gt; for <a class=\"enum\" href=\"budlang/enum.Error.html\" title=\"enum budlang::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budlang/trait.Environment.html\" title=\"trait budlang::Environment\">Environment</a>,</span>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;LinkError&gt; for <a class=\"enum\" href=\"budlang/enum.Error.html\" title=\"enum budlang::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budlang/trait.Environment.html\" title=\"trait budlang::Environment\">Environment</a>,</span>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Error&lt;'a, <a class=\"struct\" href=\"budlang/struct.BudEnvironment.html\" title=\"struct budlang::BudEnvironment\">BudEnvironment</a>&lt;Env&gt;, ReturnType&gt;&gt; for <a class=\"enum\" href=\"budlang/enum.Error.html\" title=\"enum budlang::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budlang/trait.Environment.html\" title=\"trait budlang::Environment\">Environment</a>,</span>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Fault&lt;'a, <a class=\"struct\" href=\"budlang/struct.BudEnvironment.html\" title=\"struct budlang::BudEnvironment\">BudEnvironment</a>&lt;Env&gt;, ReturnType&gt;&gt; for <a class=\"enum\" href=\"budlang/enum.Error.html\" title=\"enum budlang::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budlang/trait.Environment.html\" title=\"trait budlang::Environment\">Environment</a>,</span>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;FaultKind&gt; for <a class=\"enum\" href=\"budlang/enum.Error.html\" title=\"enum budlang::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budlang/trait.Environment.html\" title=\"trait budlang::Environment\">Environment</a>,</span>"]],
"budvm":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"budvm/lexer_util/enum.DecodeStringError.html\" title=\"enum budvm::lexer_util::DecodeStringError\">DecodeStringError</a>&gt; for <a class=\"enum\" href=\"budvm/ir/asm/enum.AsmError.html\" title=\"enum budvm::ir::asm::AsmError\">AsmError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"budvm/lexer_util/enum.DecodeNumericError.html\" title=\"enum budvm::lexer_util::DecodeNumericError\">DecodeNumericError</a>&gt; for <a class=\"enum\" href=\"budvm/ir/asm/enum.AsmError.html\" title=\"enum budvm::ir::asm::AsmError\">AsmError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.66.0/std/primitive.i64.html\">i64</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.Literal.html\" title=\"enum budvm::ir::Literal\">Literal</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.66.0/std/primitive.f64.html\">f64</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.Literal.html\" title=\"enum budvm::ir::Literal\">Literal</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.66.0/std/primitive.bool.html\">bool</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.Literal.html\" title=\"enum budvm::ir::Literal\">Literal</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.66.0/alloc/string/struct.String.html\" title=\"struct alloc::string::String\">String</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.Literal.html\" title=\"enum budvm::ir::Literal\">Literal</a>"],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.66.0/std/primitive.str.html\">str</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.Literal.html\" title=\"enum budvm::ir::Literal\">Literal</a>"],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"enum\" href=\"budvm/ir/enum.ValueSource.html\" title=\"enum budvm::ir::ValueSource\">ValueSource</a>&gt; for <a class=\"enum\" href=\"budvm/enum.ValueSource.html\" title=\"enum budvm::ValueSource\">ValueSource</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"budvm/ir/enum.Literal.html\" title=\"enum budvm::ir::Literal\">Literal</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.LiteralOrSource.html\" title=\"enum budvm::ir::LiteralOrSource\">LiteralOrSource</a>"],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"enum\" href=\"budvm/ir/enum.Literal.html\" title=\"enum budvm::ir::Literal\">Literal</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.LiteralOrSource.html\" title=\"enum budvm::ir::LiteralOrSource\">LiteralOrSource</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"budvm/ir/struct.Argument.html\" title=\"struct budvm::ir::Argument\">Argument</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.LiteralOrSource.html\" title=\"enum budvm::ir::LiteralOrSource\">LiteralOrSource</a>"],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"struct\" href=\"budvm/ir/struct.Argument.html\" title=\"struct budvm::ir::Argument\">Argument</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.LiteralOrSource.html\" title=\"enum budvm::ir::LiteralOrSource\">LiteralOrSource</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"budvm/ir/struct.Variable.html\" title=\"struct budvm::ir::Variable\">Variable</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.LiteralOrSource.html\" title=\"enum budvm::ir::LiteralOrSource\">LiteralOrSource</a>"],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"struct\" href=\"budvm/ir/struct.Variable.html\" title=\"struct budvm::ir::Variable\">Variable</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.LiteralOrSource.html\" title=\"enum budvm::ir::LiteralOrSource\">LiteralOrSource</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"budvm/ir/struct.Variable.html\" title=\"struct budvm::ir::Variable\">Variable</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.Destination.html\" title=\"enum budvm::ir::Destination\">Destination</a>"],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"struct\" href=\"budvm/ir/struct.Variable.html\" title=\"struct budvm::ir::Variable\">Variable</a>&gt; for <a class=\"enum\" href=\"budvm/ir/enum.Destination.html\" title=\"enum budvm::ir::Destination\">Destination</a>"],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"enum\" href=\"budvm/ir/enum.Destination.html\" title=\"enum budvm::ir::Destination\">Destination</a>&gt; for <a class=\"enum\" href=\"budvm/enum.Destination.html\" title=\"enum budvm::Destination\">Destination</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.66.0/core/num/dec2flt/struct.ParseFloatError.html\" title=\"struct core::num::dec2flt::ParseFloatError\">ParseFloatError</a>&gt; for <a class=\"enum\" href=\"budvm/lexer_util/enum.DecodeNumericError.html\" title=\"enum budvm::lexer_util::DecodeNumericError\">DecodeNumericError</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.66.0/core/num/error/struct.ParseIntError.html\" title=\"struct core::num::error::ParseIntError\">ParseIntError</a>&gt; for <a class=\"enum\" href=\"budvm/lexer_util/enum.DecodeNumericError.html\" title=\"enum budvm::lexer_util::DecodeNumericError\">DecodeNumericError</a>"],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.66.0/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"budvm/struct.Symbol.html\" title=\"struct budvm::Symbol\">Symbol</a>"],["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.66.0/std/primitive.str.html\">str</a>&gt; for <a class=\"enum\" href=\"budvm/enum.ValueKind.html\" title=\"enum budvm::ValueKind\">ValueKind</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"budvm/struct.Symbol.html\" title=\"struct budvm::Symbol\">Symbol</a>&gt; for <a class=\"enum\" href=\"budvm/enum.ValueKind.html\" title=\"enum budvm::ValueKind\">ValueKind</a>"],["impl&lt;'a, Intrinsic&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a [<a class=\"enum\" href=\"budvm/enum.Instruction.html\" title=\"enum budvm::Instruction\">Instruction</a>&lt;Intrinsic&gt;]&gt; for <a class=\"enum\" href=\"budvm/enum.Instructions.html\" title=\"enum budvm::Instructions\">Instructions</a>&lt;'a, Intrinsic&gt;"],["impl&lt;'a, Intrinsic&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a <a class=\"struct\" href=\"https://doc.rust-lang.org/1.66.0/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;<a class=\"enum\" href=\"budvm/enum.Instruction.html\" title=\"enum budvm::Instruction\">Instruction</a>&lt;Intrinsic&gt;, <a class=\"struct\" href=\"https://doc.rust-lang.org/1.66.0/alloc/alloc/struct.Global.html\" title=\"struct alloc::alloc::Global\">Global</a>&gt;&gt; for <a class=\"enum\" href=\"budvm/enum.Instructions.html\" title=\"enum budvm::Instructions\">Instructions</a>&lt;'a, Intrinsic&gt;"],["impl&lt;'a, Intrinsic, const SIZE:&nbsp;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.66.0/std/primitive.usize.html\">usize</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'a [<a class=\"enum\" href=\"budvm/enum.Instruction.html\" title=\"enum budvm::Instruction\">Instruction</a>&lt;Intrinsic&gt;; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.66.0/std/primitive.array.html\">SIZE</a>]&gt; for <a class=\"enum\" href=\"budvm/enum.Instructions.html\" title=\"enum budvm::Instructions\">Instructions</a>&lt;'a, Intrinsic&gt;"],["impl&lt;'a, Intrinsic&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.66.0/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;<a class=\"enum\" href=\"budvm/enum.Instruction.html\" title=\"enum budvm::Instruction\">Instruction</a>&lt;Intrinsic&gt;, <a class=\"struct\" href=\"https://doc.rust-lang.org/1.66.0/alloc/alloc/struct.Global.html\" title=\"struct alloc::alloc::Global\">Global</a>&gt;&gt; for <a class=\"enum\" href=\"budvm/enum.Instructions.html\" title=\"enum budvm::Instructions\">Instructions</a>&lt;'a, Intrinsic&gt;"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"budvm/enum.FaultKind.html\" title=\"enum budvm::FaultKind\">FaultKind</a>&gt; for <a class=\"struct\" href=\"budvm/struct.Fault.html\" title=\"struct budvm::Fault\">Fault</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budvm/trait.Environment.html\" title=\"trait budvm::Environment\">Environment</a>,</span>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.66.0/std/io/error/struct.Error.html\" title=\"struct std::io::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"budvm/enum.FaultKind.html\" title=\"enum budvm::FaultKind\">FaultKind</a>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"budvm/ir/enum.LinkError.html\" title=\"enum budvm::ir::LinkError\">LinkError</a>&gt; for <a class=\"enum\" href=\"budvm/enum.Error.html\" title=\"enum budvm::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budvm/trait.Environment.html\" title=\"trait budvm::Environment\">Environment</a>,</span>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"budvm/struct.Fault.html\" title=\"struct budvm::Fault\">Fault</a>&lt;'a, Env, ReturnType&gt;&gt; for <a class=\"enum\" href=\"budvm/enum.Error.html\" title=\"enum budvm::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budvm/trait.Environment.html\" title=\"trait budvm::Environment\">Environment</a>,</span>"],["impl&lt;'a, Env, ReturnType&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.66.0/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"budvm/enum.FaultKind.html\" title=\"enum budvm::FaultKind\">FaultKind</a>&gt; for <a class=\"enum\" href=\"budvm/enum.Error.html\" title=\"enum budvm::Error\">Error</a>&lt;'a, Env, ReturnType&gt;<span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;Env: <a class=\"trait\" href=\"budvm/trait.Environment.html\" title=\"trait budvm::Environment\">Environment</a>,</span>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()