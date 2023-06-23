import sys

output_filename = sys.argv[1]
expected_filename = sys.argv[2]

with open(output_filename) as f:
    output_contents = f.read()

with open(expected_filename) as f:
    expected_contents = f.read()


if output_contents == expected_contents:
    print("OK")
else:
    print("-- OUTPUT ------------------------------------")
    print(output_contents)
    
    print("-- EXPECTED ----------------------------------")
    print(expected_contents)
