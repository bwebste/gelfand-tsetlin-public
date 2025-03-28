import argparse
from itertools import permutations
from collections import defaultdict
import fractions
from concurrent.futures import ProcessPoolExecutor
import os
import time
import resource
import pickle

class LaurentPolynomial:
    """Represents a Laurent polynomial in q with integer coefficients"""
    def __init__(self, coeffs=None):
        self.coeffs = defaultdict(int)
        if coeffs:
            for power, coeff in coeffs.items():
                if coeff != 0:
                    self.coeffs[power] = coeff
    
    def __add__(self, other):
        result = LaurentPolynomial()
        powers = set(self.coeffs.keys()) | set(other.coeffs.keys())
        for power in powers:
            coeff = self.coeffs[power] + other.coeffs[power]
            if coeff != 0:
                result.coeffs[power] = coeff
        return result
    
    def __mul__(self, other):
        result = LaurentPolynomial()
        for p1, c1 in self.coeffs.items():
            for p2, c2 in other.coeffs.items():
                result.coeffs[p1 + p2] += c1 * c2
        return result
    
    def __neg__(self):
        result = LaurentPolynomial()
        for power, coeff in self.coeffs.items():
            result.coeffs[power] = -coeff
        return result
    
    def __truediv__(self, other):
        if not isinstance(other, LaurentPolynomial):
            raise TypeError("Can only divide by another LaurentPolynomial")
        
        result = LaurentPolynomial()
        remainder = LaurentPolynomial(self.coeffs.copy())
    
                # Get the highest degree term of the divisor
        divisor_highest_power = max(other.coeffs.keys())
        divisor_highest_coeff = other.coeffs[divisor_highest_power]
        if not remainder.coeffs:
            return LaurentPolynomial()
        remainder_spread=max(remainder.coeffs.keys())-min(remainder.coeffs.keys())
        divisor_spread=max(other.coeffs.keys())-min(other.coeffs.keys())
        
        while remainder.coeffs:
            # Get the highest degree term of the remainder
            remainder_highest_power = max(remainder.coeffs.keys())
            remainder_highest_coeff = remainder.coeffs[remainder_highest_power]
            
            # Compute the term to subtract
            quotient_power = remainder_highest_power - divisor_highest_power
            quotient_coeff = remainder_highest_coeff / divisor_highest_coeff
            
            quotient_term = LaurentPolynomial({quotient_power: int(quotient_coeff)})
            result += quotient_term
            
            # Subtract the term from the remainder
            remainder -= quotient_term * other
            if remainder.coeffs.keys():
                if remainder_spread <= max(remainder.coeffs.keys())-min(remainder.coeffs.keys()):
                    raise ValueError("Division seems to have failed.  Numerator=", str(self), ", Denominator=", str(other), ", Quotient=", str(result), ", Remainder=", str(remainder))
                else: 
                    remainder_spread=max(remainder.coeffs.keys())-min(remainder.coeffs.keys())
        #print("self=",self," other=",other," remainder=",remainder, " result=",result)
        return result
    
    def __sub__(self, other):
        return self + (-other)
    
    def __str__(self):
        if not self.coeffs:
            return "0"
        terms = []
        for power, coeff in sorted(self.coeffs.items()):
            if coeff == 0:
                continue
            if power == 0:
                terms.append(str(coeff))
            elif power == 1:
                terms.append(f"{coeff if coeff != 1 else ''}q")
            elif power == -1:
                terms.append(f"{coeff if coeff != 1 else ''}q^(-1)")
            else:
                terms.append(f"{coeff if coeff != 1 else ''}q^({power})")
        return " + ".join(terms) if terms else "0"
    
    def __eq__(self,other):
        if not isinstance(other, LaurentPolynomial):
            return False
        return self.coeffs == other.coeffs
    
    def __hash__(self):
        return hash(frozenset(self.coeffs.items()))


    def evaluate_at_q1(self):
        """Evaluate the Laurent polynomial at q=1"""
        return sum(self.coeffs.values())


def generate_decreasing_sequences(max_val):
    """Generate all strictly decreasing consecutive sequences of given length with maximum value"""
    GL= []
    GL_prime = []
    for top in range(1, max_val):
        for first in range(1, top+1):
            sequence = list(range(top,first-1, -1))
            GL.append(sequence)
    top=max_val
    for first in range(1, top+1):
            sequence = list(range(top,first-1, -1))
            GL_prime.append(sequence)
    return [GL, GL_prime]

def concatenate_word(word):
    """Concatenate the parts of a red-good word"""
    gl_parts, glp_parts = word
    return tuple(sum(gl_parts,[]) + sum(glp_parts,[]))

def generate_red_good_words(n, v_counts, k):
    """Generate all red-good words with given letter counts"""
    result = []
    
    if any(count < 0 for count in v_counts) or all(count == 0 for count in v_counts):
        return
    lyndon=generate_decreasing_sequences(n)
    GL=lyndon[0]
    GL_prime=lyndon[1]
    # Generate all possible GL and GL' parts
    for lowest in range(k,len(GL)+1):
        if lowest< len(GL):
            new_v_counts = v_counts.copy()
            for i in GL[lowest]:
                new_v_counts[i-1] -= 1
            if all(count >= 0 for count in new_v_counts):
                if all(count == 0 for count in new_v_counts):
                    result.append(([GL[lowest]],[]))
                else:
                    subresult=generate_red_good_words(n, new_v_counts, lowest)
                    for x in subresult:
                        x[0].insert(0,GL[lowest])
                        result.append(x)
        else: 
            for first in range(len(GL_prime)):
                new_v_counts = v_counts.copy()
                for i in GL_prime[first]:
                    new_v_counts[i-1] -= 1
                if all(count == 0 for count in new_v_counts):
                    result.append(([],[GL_prime[first]]))
                else:
                    if all(count >= 0 for count in new_v_counts):
                        subresult=generate_red_good_words(n, new_v_counts, lowest)
                        for x in subresult:
                            x[1].insert(0,GL_prime[first])
                            result.append(x)
    return sorted(result, key=concatenate_word, reverse=True)
import subprocess

def sync_to_server():
    """Sync the local directory to the remote server using rsync."""
    local_dir = "/Users/benwebster/b2webste"
    remote_dir = "b2webste@biglinux.math.uwaterloo.ca:/u/b2webste"
    remote_dir2 = "b2webste@rsubmit.math.private.uwaterloo.ca:/work/b2webste"

    from_local_dir = "/Users/benwebster"
    from_remote_dir = "b2webste@biglinux.math.uwaterloo.ca:/u/b2webste/b2webste"
    from_remote_dir2 = "b2webste@rsubmit.math.private.uwaterloo.ca:/u/b2webste/b2webste"
    try:
        print("Trying to sync to server...")
        subprocess.run(
            ["rsync", "-avz", local_dir, remote_dir],
            check=True
        )
        subprocess.run(
            ["rsync", "-avz", local_dir, remote_dir2],
            check=True
        )
        print("Trying to sync from server...")
        subprocess.run(
            ["rsync", "-avz", from_remote_dir, from_local_dir],
            check=True
        )
        subprocess.run(
            ["rsync", "-avz", from_remote_dir2, from_local_dir],
            check=True
        )
        # print("Sync completed successfully.")
    except subprocess.CalledProcessError as e:
        print(f"Error during sync: {e}")

def shuffle_words(word1, word2, n, degree=0):
    """Generate all possible shuffles of two words with their degrees"""

    if not word1:
        yield word2, degree
        return
    if not word2:
        yield word1, degree
        return
    
    # Take from first word
    for rest, rest_degree in shuffle_words(word1[1:], word2, n, degree):
        yield [word1[0]] + rest, rest_degree
    
    # Take from second word
    x = word2[0]
    if x < n or all(entry != n for entry in word1):
        count_x_plus_minus_1 = word1.count(x + 1) + word1.count(x - 1)
        count_x = word1.count(x)
        new_degree = degree + count_x_plus_minus_1 - 2 * count_x
        for rest, rest_degree in shuffle_words(word1, word2[1:], n, new_degree):
            yield [x] + rest, rest_degree

def shuffle_generator(generator, word2, n):
    """Generate all possible shuffles of a generator with a word"""
    #print("applying shuffle_generator to",generator,word2)
    for word1, degree in generator:
        #print("word1=",word1," word2=",word2)
        for shuffled, new_degree in shuffle_words(word1, word2, n, degree):
            yield shuffled, new_degree

def shuffle_dicts(dict1, dict2,n):
    """Shuffle two dictionaries"""
    result = defaultdict(LaurentPolynomial)
    #print("shuffling ", str(dict1), " and ", str(dict2))
    for word1, poly1 in dict1.items():
        for word2, poly2 in dict2.items():
            #print("shuffling ", word1, " and ", word2)
            for shuffled, degree in shuffle_words(list(word1), list(word2),n):
                result[tuple(shuffled)] += poly1 * poly2 * LaurentPolynomial({degree: 1})
    return dict(result)

def multiplicity_factor(gl_parts):
    # Compute multiplicity factor
    multiplicity_factor = LaurentPolynomial({0:1})
    degree=0
    i=1
    current_run = 1
    while i < len(gl_parts):
        if gl_parts[i] == gl_parts[i-current_run]:
            current_run += 1
            i += 1
            multiplicity_factor *= LaurentPolynomial({-2*p: 1 for p in range(current_run)})
            degree = degree + current_run -1
        else: 
            current_run = 1
            i += 1
    multiplicity_factor = multiplicity_factor* LaurentPolynomial({degree:1})
    return multiplicity_factor, degree

def dict_from_word(word):
    """Convert a word to a dictionary with a single term"""
    return {tuple(word): LaurentPolynomial({0: 1})}

def compute_standard_character(gl_parts, glp_parts, n):
    """Compute the character of a standard module"""
    result = defaultdict(LaurentPolynomial)
    mult, multdegree = multiplicity_factor(gl_parts)
    
    # Convert gl_parts and glp_parts to dictionaries
    gl_dicts = [dict_from_word(part) for part in gl_parts]
    glp_dicts = [dict_from_word(part) for part in glp_parts]
    #print("working on standard character for ", concatenate_word((gl_parts, glp_parts)))
    #print(str(gl_dicts), str(glp_dicts))
    shuffled_dict = {(): LaurentPolynomial({0: 1})}
    for gl_dict in gl_dicts:
        shuffled_dict = shuffle_dicts(shuffled_dict, gl_dict, n)
        #print(format_character(shuffled_dict))
    for glp_dict in glp_dicts:
        shuffled_dict = shuffle_dicts(shuffled_dict, glp_dict, n)
        #
        # print(format_character(shuffled_dict))
        #print(str(shuffled_dict))

    # Multiply by the multiplicity factor
    for word, poly in shuffled_dict.items():
        result[word] += poly * LaurentPolynomial({multdegree: 1})

    # Generate shuffles and compute weights
    # if len(gl_parts) >= 1:
    #     shuffles = list(shuffle_words(gl_parts[0], [], n))
    #     print("working on standard character for ", concatenate_word((gl_parts, glp_parts)), " just did", gl_parts[0])
    #     for i in range(1, len(gl_parts)):
    #         shuffles = list(shuffle_generator(shuffles, gl_parts[i], n))
    #         print("working on standard character for ", concatenate_word((gl_parts, glp_parts)), " just did", gl_parts[i])
    #     shuffles = list(shuffle_generator(shuffles, glp_parts[0], n))
    #     print("working on standard character for ", concatenate_word((gl_parts, glp_parts)), " just did", gl_parts, glp_parts[0])
    # else:
    #     shuffles = list(shuffle_words(glp_parts[0], [], n))
    #     print("working on standard character for ", concatenate_word((gl_parts, glp_parts)), " just did", gl_parts, glp_parts[0])
    # for i in range(1, len(glp_parts)):
    #     shuffles = list(shuffle_generator(shuffles, glp_parts[i], n))
    #     print("working on standard character for ", concatenate_word((gl_parts, glp_parts)), " just did", gl_parts, glp_parts[i])
    # mult, multdegree = multiplicity_factor(gl_parts)
    # for shuffled, degree in shuffles:
    #     weight = LaurentPolynomial({degree + multdegree: 1})
    #     result[tuple(shuffled)] += weight
    #print("done with standard character for ", concatenate_word((gl_parts, glp_parts)))
    return result
def is_bar_invariant(polynomial):
    """Check if a polynomial is bar-invariant"""
    return all(polynomial.coeffs[power]==polynomial.coeffs[-power] for power in polynomial.coeffs.keys())

def closer_to_a_simple(current_char, red_good_words, n):
    """Check if a character is closer to a simple character than a standard character"""
    for i in range(len(red_good_words) - 1, -1, -1):
        word = red_good_words[i]
        c_word = concatenate_word(word)
        v_count = [c_word.count(i) for i in range(1, n + 1)]
        if not is_bar_invariant(current_char[c_word]):
            file_handle = f"simple_character_{c_word}_v_counts_{v_count}.pkl"
            directory_name = f"_binary_{v_count}"
            file_name = os.path.join(directory_name, file_handle)

            if not os.path.exists(file_name):
                print(f"File {file_name} not found. Retrying...")
                raise RuntimeError(f"File {file_name} not found.")

            lower_char = read_file(file_name)
            if lower_char is None:
                raise RuntimeError(f"File {file_name} is empty or corrupted.")

            coefficient = current_char[c_word]
            simple_mult = LaurentPolynomial()
            mod_coefficient = LaurentPolynomial(coefficient.coeffs.copy())
            mult, multdegree = multiplicity_factor(word[0])
            q = 1
            while not is_bar_invariant(mod_coefficient):
                q += 1
                maxi = max(
                    power
                    for power in mod_coefficient.coeffs.keys()
                    if -power not in mod_coefficient.coeffs.keys()
                    or mod_coefficient.coeffs[power] != mod_coefficient.coeffs[-power]
                )
                simple_mult += LaurentPolynomial(
                    {maxi - multdegree: mod_coefficient.coeffs[maxi] - mod_coefficient.coeffs[-maxi]}
                )
                mod_coefficient = LaurentPolynomial(coefficient.coeffs.copy()) - simple_mult * mult
                if q > 10000:
                    raise ValueError("This has gone on too long")
            for wordies in lower_char.keys():
                current_char[wordies] = current_char[wordies] + (-simple_mult * lower_char[wordies])
                if any(coeff < 0 for coeff in current_char[wordies].coeffs.values()):
                    raise ValueError("These coefficients are supposed to be non-negative")
            return current_char
    return current_char

def compute_one_simple_character(red_good_words, i, n):
    """Compute the character of a simple module"""
    word = red_good_words[i]
    gl_parts, glp_parts = word
    wordie = concatenate_word(word)
    v_count = [wordie.count(i) for i in range(1, n + 1)]
    file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
    directory_name = f"_binary_{v_count}"
    file_name = os.path.join(directory_name, file_handle)

    if not os.path.exists(directory_name):
        os.makedirs(directory_name)

    current_char = read_file(file_name)
    if current_char is not None:
        print("already computed simple character for ", wordie)
        return current_char

    print("computing standard character for ", wordie)
    standard_char = compute_standard_character(gl_parts, glp_parts, n)
    current_char = standard_char.copy()

    size = 50
    g = i / size
    for j in range(i, -1, -1):
        maybe_char = read_file(file_name)
        if maybe_char is not None:
            print("already computed simple character for ", wordie)
            return maybe_char
        for k in range(size):
            if i - j == int(k * g):
                print(i, ": [", k * ".", (size - k) * " ", "]", time.strftime("%H:%M:%S", time.localtime()))
        lower_word = red_good_words[j]
        lower_wordies = concatenate_word(lower_word)
        if not is_bar_invariant(current_char[lower_wordies]):
            print(i, " minus ", j," ",lower_wordies)
            try:
                current_char = closer_to_a_simple(current_char, red_good_words, n)
            except RuntimeError as e:
                print(f"Error: {e}")
                raise RuntimeError(f"File {file_name} not found. Retrying...")
    sync_to_server()
    print("done computing simple character for ", wordie)
    write_file(file_name, current_char)
    return current_char

def compute_simple_characters(standard_chars,red_good_words):
    set_memory_limit(500 * 1024 * 1024) 
    """Compute characters of simple modules"""
    simple_chars = {}
    words = sorted(standard_chars.keys())
    
    for i in range(len(red_good_words)):
        word=red_good_words[i]
        standard_char = standard_chars[concatenate_word(word)]
        current_char = standard_char.copy()
        simple_mults=[0]*(len(red_good_words))
        mults=[0]*(len(red_good_words))
        lower_chars=[0]*(len(red_good_words))
        # Subtract appropriate multiples of lower standard characters
        for j in range(i-1, -1, -1):
            #print(i,j)
            print("computing simple character for ", word, " subtracting ", red_good_words[j])
            lower_word = red_good_words[j]
            lower_char = simple_chars[concatenate_word(lower_word)]
            # Find bar-invariant polynomial
            lw = concatenate_word(lower_word)
            coefficient = current_char[lw]
            simple_mult = LaurentPolynomial()
            mod_coefficient = LaurentPolynomial(coefficient.coeffs.copy())
            mult,  multdegree = multiplicity_factor(lower_word[0])
            q=1
            while not is_bar_invariant(mod_coefficient):
                q+=1
                #print(str(mod_coefficient),",",str(mult))
                maxi=max(power for power in mod_coefficient.coeffs.keys() if -power not in mod_coefficient.coeffs.keys() or mod_coefficient.coeffs[power] != mod_coefficient.coeffs[-power])
                simple_mult+=LaurentPolynomial({maxi-multdegree:mod_coefficient.coeffs[maxi]-mod_coefficient.coeffs[-maxi]})
                mod_coefficient = LaurentPolynomial(coefficient.coeffs.copy())-simple_mult*mult
                simple_mults[j]=simple_mult
                mults[j]=mult
                if q>9990:
                    print("coeff=",str(coefficient),", mult=",str(mult),", simple_mult=",str(simple_mult),", mod_coefficient=",str(mod_coefficient))
                if q>10000:
                    raise ValueError("This has gone on too long")

            for wordies in lower_char.keys():
                current_char[wordies] = current_char[wordies] + (-simple_mult*lower_char[wordies])
                if any(coeff < 0 for coeff in current_char[wordies].coeffs.values()):#                 
                    print("wordies=",wordies,", upper words=",concatenate_word(word),", lower word=",lw)
                    print("weight multiplicities for ", wordies)
                    print(concatenate_word(red_good_words[i]), "   ", str(standard_char[wordies]))
                    for q in range(i+1,j+1):
                        low_word = concatenate_word(red_good_words[q])
                        print(concatenate_word(low_word),"   ", str(simple_mults[q])," * ",str(simple_chars[low_word][wordies]))
                    print(" " * (len(str(wordies))+3), str(current_char[wordies]))

                    print("weight multiplicities for ", lw)
                    print(concatenate_word(red_good_words[i]), "   ", str(standard_char[lw]))
                    for q in range(i+1,j+1):
                        low_word = concatenate_word(red_good_words[q])
                        print(low_word,"   ", str(simple_mults[q])," * ",str(simple_chars[low_word][lw]))
                    print(" " * (len(str(wordies))+3), str(current_char[lw]))
                    raise ValueError("These coefficients are supposed to be non-negative")
            #print("done subtracting simple character for ", word, " from ", lower_word)
            #if i==0:
                #print(format_character(current_char))
            #for q in red_good_words[i:j+1]:
                #print(str(current_char[concatenate_word(q)]))
                # if not is_bar_invariant(current_char[concatenate_word(q)]):
                #     print("subtracting ", simple_mult*lower_char[q], " from ", q,"to get ", current_char[q])
                #     raise ValueError("Failed to find bar-invariant polynomial")
                    
        #print("simple character for ", word, " added at i=", i)
        simple_chars[concatenate_word(word)] = {k: v for k, v in current_char.items() if clean_polynomial(v) != LaurentPolynomial()}
    return simple_chars


def format_character(char):
    """Format a character for printing"""
    return "\n".join(f"{word}: {char[word]}" for word in sorted(char.keys()) if char[word] != 0)


def compute_standard_character_for_word(word,n):
    """Helper function to compute the standard character for a single word"""
    return concatenate_word(word), compute_standard_character(word[0], word[1],n)

def clean_polynomial(polynomial):
    """Remove terms with zero coefficients"""
    return LaurentPolynomial({power: coeff for power, coeff in polynomial.coeffs.items() if coeff != 0})

def find_dimensions(simple_char):
    flattened_values = [clean_polynomial(value) for value in simple_char.values()]
    unique_values = set(flattened_values)
    return unique_values

def set_memory_limit(max_memory):
    """Set the maximum memory limit for the current process."""
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (max_memory, hard))

def read_file(file_name):
    """Read the content of a file using pickle and return it."""
    if os.path.exists(file_name):
        try:
            with open(file_name, "rb") as file:  # Use "rb" for reading binary files
                return pickle.load(file)  # Deserialize the binary data
        except Exception as e:
            os.remove(file_name)
            print(f"Something wrong with {file_name}: {e}")
    return None

def write_file(file_name, data):
    """Write data to a file using pickle."""
    with open(file_name, "wb") as file:  # Use "wb" for writing binary files
        pickle.dump(data, file)  # Serialize the data

def main_parallel(n, v_counts):
    sync_to_server()
    red_good_words = generate_red_good_words(n, v_counts, 0)
    unique_values = {}
    j=0
    for i in range(len(red_good_words)):
        word = red_good_words[i]
        wordie = concatenate_word(word)
        v_count = [wordie.count(i) for i in range(1, n + 1)]
        file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"  # Use .pkl for binary files
        directory_name = f"_binary_{v_count}"
        if not os.path.exists(directory_name):
            os.makedirs(directory_name)
        file_name = os.path.join(directory_name, file_handle)
        unique_values[i] = read_file(file_name)  # Use read_file
        if unique_values[i] is None:
            j = i
            break
    print("----------------restarting with j=", j)
    time.sleep(1)
    with ProcessPoolExecutor(max_workers=2) as executor:
        mini = min(j + 400, len(red_good_words))
        futures = [executor.submit(compute_one_simple_character, red_good_words, i, n) for i in range(j, mini)]
        for i, future in enumerate(futures):
            word = red_good_words[i + j]
            wordie = concatenate_word(word)
            print("doing ", i, "th red-good-word:", wordie)
            try:
                v_count = [wordie.count(i) for i in range(1, n + 1)]
                file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"
                directory_name = f"_binary_{v_count}"
                file_name = os.path.join(directory_name, file_handle)
                if not os.path.exists(directory_name):
                    os.makedirs(directory_name)
                if not os.path.exists(file_name):
                    unique_values[i] = find_dimensions(future.result())
                    print("done computing unique values for ", concatenate_word(red_good_words[i]))
                    write_file(file_name, unique_values[i])  # Use write_file
                    print("wrote unique values for ", wordie)
            except Exception as e:
                print(f"Error processing {file_name}: {e}")
    if mini == len(red_good_words):
        full_unique_values = set(x for i in range(len(red_good_words)) for x in unique_values[i])
        print("\nUnique values of characters:")
        values = [str(value) + " = " + str(value.evaluate_at_q1()) for value in full_unique_values if isinstance(value, LaurentPolynomial)] + \
                [str(value) for value in full_unique_values if not isinstance(value, LaurentPolynomial)]
        print("\n".join(values))
        file_name = f"results_{n}_vcounts_{v_counts}.pkl"
        write_file(file_name, full_unique_values)  # Use write_file
    print("All done!")

def main(n, v_counts):
    sync_to_server()
    """Main function to compute all characters"""
    print(f"Computing characters for n={n} with counts {v_counts}")
    red_good_words = generate_red_good_words(n, v_counts, 0)
    unique_values = {}
    j=0
    for i in range(len(red_good_words)):
        word = red_good_words[i]
        wordie = concatenate_word(word)
        v_count = [wordie.count(i) for i in range(1, n + 1)]
        file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"
        directory_name = f"_binary_{v_count}"
        file_name = os.path.join(directory_name, file_handle)

        unique_values[i] = read_file(file_name)
        if unique_values[i] is None:
            j=i
            break
    print("j=",j)
    #for i in range(j, len(red_good_words)):
    word = red_good_words[j]
    wordie = concatenate_word(word)
    v_count = [wordie.count(i) for i in range(1, n + 1)]
    file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"
    directory_name = f"_binary_{v_count}"
    file_name = os.path.join(directory_name, file_handle)

    if not os.path.exists(directory_name):
        os.makedirs(directory_name)

    print("doing ", j, "th red-good-word:", wordie)
    try:
        unique_values[j] = find_dimensions(compute_one_simple_character(red_good_words, j, n))
        print("done computing unique values for ", concatenate_word(red_good_words[j]))
        write_file(file_name, unique_values[j])
        print("wrote unique values for ", wordie)
    except Exception as e:
        print(f"Didn't work to process {file_name}, guess I'll try again: {e}")

    # full_unique_values = set(x for i in range(len(red_good_words)) for x in unique_values[i])
    # print("\nUnique values of characters:")
    # values = [str(value) + " = " + str(value.evaluate_at_q1()) for value in full_unique_values if isinstance(value, LaurentPolynomial)] + \
    #          [str(value) for value in full_unique_values if not isinstance(value, LaurentPolynomial)]
    # print("\n".join(values))

    # file_name = f"results_{n}_vcounts_{v_counts}.pkl"
    # write_file(file_name, full_unique_values)
    print("On to the next one!")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Compute characters of simple modules.")
    parser.add_argument("mode", choices=["main", "main_parallel"], help="Mode to run the script in.")
    parser.add_argument("n", type=int, help="Value of n.")
    parser.add_argument("v_counts", type=int, nargs="+", help="List of counts.")

    args = parser.parse_args()
    while True:
        if args.mode == "main":
            main(args.n, args.v_counts)
        elif args.mode == "main_parallel":
            main_parallel(args.n, args.v_counts)

