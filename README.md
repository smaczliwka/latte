# Kompilator Latte

### KOMPILACJA
W przypadku budowania kompilatora poza maszyną students należy przed wywołaniem `make` ustawić pod zmienną środowiskową BNFC ścieżkę do bnfc. Po zbudowaniu kompilatora poleceniem `make` w korzeniu znajduje się plik wykonywalny `latc_llvm`.

### URUCHAMIANIE
- Wykonanie `latc_llvm foo/bar/baz.lat` dla poprawnego programu wejściowego `baz.lat` generuje pliki `baz.ll` (kod LLVM) oraz `baz.bc` (bitkod LLVM wykonywalny przy uzyciu lli) w katalogu `foo/bar`.
- Jeśli kompilator akceptuje program, wypisuje w pierwszej linii `stderr` napis `"OK"` i kończy się z kodem powrotu `0`.
- Jeśli kompilator odrzuca program, wypisuje w pierwszej linii `stderr` napis `ERROR`, a w kolejnej informację o błędzie umożliwiającą jego lokalizację i kończy się z kodem powrotu różnym od `0`.

### STRUKTURA KATALOGU
- **`src/Latte.cf`** - gramatyka języka Latte w postaci BNFC
- **`src/Main.hs`** - moduł obsługujący argumenty wiersza poleceń i generujący pliki `.ll` oraz `.bc` korzystając z modułów `Emiter`, `Oprimizer` i `Printer` oraz poleceń `llvm-as` i `llvm-link`
- **`src/Typechecker.hs`** - moduł wykrywający statycznie wykrywalne błędy programu (błędy typów, nieznany identyfikator, zła liczba argumentów itp.)
- **`src/Emiter.hs`** - moduł generujący kod czwórkowy programu w postaci SSA
- **`src/Optimizer.hs`** - moduł wykonujący optymalizacje na kodzie czwórkowym wygenerowanym przez `Emiter` (LCSE/GCSE i usuwanie martwego kodu)
- **`src/Printer.hs`** - moduł konwertujący kod czwórkowy wygenerowany przez `Emiter` na poprawny kod LLVM
- **`lib/runtime.bc`** - moduł zawierający funkcje predefiniowane w Latte oraz funkcje pomocnicze służące do porównywania i konkatenacji napisów, linkowany do kodu wykonywalnego w trakcie kompilacji poleceniem `llvm-link`
- **`lib/runtime.ll`** - kod źródłowy modułu `lib/runtime.ll`
- **`tests`** - folder z własnymi testami pokazującymi działanie optymalizacji
- **`Makefile`** - pozwalający na zbudowanie programu

### ROZSZERZENIA I OPTYMALIZACJE
- Użycie rejestrów i `phi` zamiast alloc.
- LCSE i GCSE z usuwaniem trywialnych `phi`
- Usuwanie martwego kodu.
- Function inlining: inline funkcje mogą wywoływać inne inline funkcje, ale cykle wywołań takich funkcji są wykrywane przez typechecker i raportowane jako błąd.
