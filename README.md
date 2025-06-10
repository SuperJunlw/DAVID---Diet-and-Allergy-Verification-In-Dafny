# DAVID---Diet-and-Allergy-Verification-In-Dafny

## Verification in Dafny
1. The fully functional verification is david.dfy
2. Have to use the run command to see the output labeled tree

```
dafny run david.dfy
```

## Running in python

1. Expects two command line arguments, first file containing menu tree and second file containing allergen list
2. Both file need to be in data directory relative to __main__.py
3. After going to the directory of david-py run the following command

```
python __main__.py burger.txt allergen_burger.txt
```
