import "hint" HLint.HLint

ignore "Redundant do"
ignore "Redundant as"
ignore "Redundant $" = LambdaCube.Compiler.Infer
ignore "Use if"
ignore "Use ++" = Main -- UnitTests
ignore = LambdaCube.Compiler.Token

--ignore "Eta reduce"
--ignore "Move brackets to avoid $"
--ignore "Redundant bracket"

