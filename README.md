# Software Specification Project 19/20

![](https://avatars0.githubusercontent.com/u/52358127?s=200&v=4)

**Table of Contents**

- [Dafny - Software Specification Project 19/20](#dafny---software-specification-project-19-20)
- [Intro](#intro)
- [Reverse a file](#reverse-a-file)
- [Pattern matching](#pattern-matching)
  * [Naive Approach](#naive-approach)
  * [Knuth-Morris-Pratt Algorithm](#knuth-morris-pratt-algorithm)
  * [Extra: Bash-style Line matching](#extra--bash-style-line-matching)
- [Conclusion / Problems Faced](#conclusion---problems-faced)
- [Authors](#authors)

# Intro
In this project we will attempt to write specifications for programs and prove that they are maintained by our implementation.\
We will use pre-conditions and post-conditions to be sure that our methods fullfill the specification and loop invariants to be sure that our loops achieve certain properties.\
A programming language with a verification tool included will be used, Dafny. 
It's an interesting language because it aims for real-world code verification as it integrates with C#.

# Reverse a file
The first challenge is to reverse a file.\
First, we should try to formulate the specification, and find out which properties we should try to keep between the original file and the reversed file.
In the initial stages of the project we actually first thought on the implementation, and then on what the are the properties that should be maintained, which is not the best way and can make the specification harder!\
So, we first though on the methods:

* Divide the input file in lines
* Reverse the lines
* Collapse the reversed lines into a single array
* Write the array into the destination file

The properties we need to maintain are then:

* For the reversing method
	* The reversed lines being returned are actually the reverse of the original lines 
	* The sum of the lengths of the reversed lines is the same as the sum of the lengths of the original lines
* For the file writing
	* The output file exists 
	* The output file contains the same number of bytes as the input file
	* The output file is actually the reverse of the input file


# Pattern matching
Then, we attempted to verify some pattern matching algorithms.\
Divided in two parts, first we attempt a simple naive approach and then a more complicated Knuth-Morris-Pratt algorithm verification.\
Here, the objective is to read a file and search for a given string and return the indexes where it is found, or just return an empty sequence if there is no match.\
We re-utilized some code from the reverse challenge, mostly on the file reading and splitting.

## Naive Approach
For this approach, the implementation is very simple, just iterate over the searched line and then check in that index if there is a match.\
This method should ensure at least two properties:
1. All returned indexes should be a match
2. If at least one index was returned, then there must be at least one index which is a match 

Essentially, there are two `while` loops that should achieve those properties.\
The first loop iterates over the searched word, and the second loop iterates over the query to find the match. \
By having the second loop as a separate method that returns a boolean if it has found a match, we can have it ensure the 1<sup>st</sup> property. This is done using an incremental loop invariant for partial match that ensures that the query matches the word in the slice `index..index+count`, count being the number of matches achieved.\
At termination, if the loop fully matched, then, we can prove there was a full match because of the invariant used.\
To prove the 2<sup>nd</sup> property, as we only append to the index sequence if the index is a full match, we can also add an invariant saying that if we found at least one index there is at least one match.

## Knuth-Morris-Pratt Algorithm
After doing a simple Naive pattern matching algorithm the next step is to try to write a verified Knuth-Morris-Pratt algorithm. \
Instead of trying to check for the query at every position in the searched string, the algorithm checks characters in the searched word and the query string at the same time.\
To prevent having to re-check previous parts of the word, this algorithm requires calculating a table before starting the search. This table contains the partial match for each index of the query, allowing the algorithm to know where it can restart the search after failing to find a match.\
To correctly verify this algorithm we need to ensure the same properties as the Naive, and some more because of the complexity introduced with the partial match table:
1. (Naive) All returned indexes should be a match
2. (Naive) If at least one index was returned, then there must be at least one index which is a match 
3. Every value greater than 0 in the partial match table means that the substring of length of the value is also a prefix of the query\
Example:
```
Query := abcabc
Table := [0, 0, 0, 1, 2, 3]
At index 4, value on Table := 2, 
then, the substring of length 2 ending at index 4 := 'ab', which is also a prefix of the query.
The same logic can be applied to other indexes which are > 0.
```

## Extra: Bash-style Line matching
There is an interesting extra to this challenge, which is instead of returning matching indexes, we return the lines of the file that match the query.\
For this, specification-wise, we should aim to verify that all the returned lines contain at least one match.\
Since Dafny doesn't support pretty colour printing we chose not to try to highlight the matches and just display the lines. Initially we tried to do something like inserting some characters to highlight but as that introduced some problems we chose to go for a simpler way.

Example of execution:

```
Word
aabca
aba
aabcd

Query
abc

Matching lines
aabca
aabcd
```

Since the line `aba` doesn't contain the query, it is not part of the matching lines returned.
# Conclusion / Problems Faced
After finishing this project we got a better insight on the topics of program verification and writing specifications that fulfill the requirements.
We wrote code that the compiler can prove that maintains some properties that will ensure that the specification is not being violated, by using some formal logic concepts.\
This isn't always easy as it requires functional thinking which sometimes isn't very easy for developers used to only OOP.\
Another problem is that Dafny is quite an experimental tool and sometimes programs a bit more complex (like programs dealing with files like our reverse) can take long time to verify or even time out because the verifier wasn't able to prove all the proof obligations of the program, which was our case for a long part of the project.\
We managed to solve some problems partially, probably by reducing the complexity of the properties our methods were ensuring.

# Authors
* David Frickert - 97033
* Diogo Faustino - 97081
