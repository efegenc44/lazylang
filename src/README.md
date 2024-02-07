# Lazy Simple Functional Programming Langauge

```
first  = \x:xs -> x
second = \x:xs -> xs

ones = 1:ones

main = \->
    first(second(ones))

```
