# Normalise the closed show-* definitions in book/show.muro.
#
# mix muro.check proves the equations. It does not print a value, and
# there is no mix muro.eval. Load.file checks the book. normalize/3
# with the checker's :run unfold then reduces each closed run String.
# A string normal form is {:slit, binary}. Anything else is a failure.
#
# stdout is the show-* lines and nothing else. Timing goes to stderr.
# Fuel is per definition, so one term cannot spend the others' budget.
# show-wide is the printer check (overflow, then ten at fuel 8).

path = Path.expand("book/show.muro")
check_fuel = 20_000
norm_fuel = 200_000

names = ~w(show-trip show-stuck show-alloc show-deref show-send show-step show-collect show-wide)

case Muro.Load.file(path, fuel: check_fuel) do
  {:error, msg} ->
    IO.puts(:stderr, "LOAD #{msg}")
    System.halt(1)

  {:ok, named} ->
    case Muro.Ast.book_to_db(Muro.Prelude.for_check(named)) do
      {:error, msg} ->
        IO.puts(:stderr, "DB #{msg}")
        System.halt(1)

      {:ok, db} ->
        Enum.each(names, fn name ->
          t0 = System.monotonic_time(:millisecond)

          case Muro.Check.normalize(db, {:def, name}, norm_fuel) do
            {:ok, {:slit, bin}} ->
              dt = System.monotonic_time(:millisecond) - t0
              IO.puts(:stderr, "NF #{name} #{dt}ms #{byte_size(bin)}b")
              IO.write(bin)

            other ->
              IO.puts(:stderr, "STUCK #{name} #{inspect(other, limit: 40)}")
              System.halt(1)
          end
        end)
    end
end
