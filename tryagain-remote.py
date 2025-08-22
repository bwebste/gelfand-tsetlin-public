import argparse
from itertools import permutations
from collections import defaultdict
import fractions
from concurrent.futures import ProcessPoolExecutor
import os
import time
import resource
import pickle
from multiprocessing import Process
from rich.progress import Progress
from multiprocessing import Queue
from multiprocessing import Manager

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
    
    def latex(self):
        if not self.coeffs:
            return "0"
        terms = []
        for power, coeff in sorted(self.coeffs.items()):
            if coeff == 0:
                continue
            if power == 0:
                terms.append(f"{coeff}")
            elif power == 1:
                terms.append(f"{coeff if coeff != 1 else ''}q")
            elif power == -1:
                terms.append(f"{coeff if coeff != 1 else ''}q^{{-1}}")
            else:
                terms.append(f"{coeff if coeff != 1 else ''}q^{{{power}}}")
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
        return []
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

def check_for_file(file_name,v_counts):
    local_dir = "/Users/b2webste/b2webste/_binary_" + str(v_counts)
    remote_dir = "b2webste@biglinux.math.uwaterloo.ca:/u/b2webste/b2webste/_binary_" + str(v_counts)
    full_path = remote_dir + "/" + file_name
    new_file_name = local_dir + "/" + file_name+".tmp"
    #print("full_path is", full_path, "new_file_name is", new_file_name)
    try: 
        command = ["scp", full_path, new_file_name]
        #print(" ".join(command))
        subprocess.run(command, check=True)
        print("File ", new_file_name, " gotten from server.")
    except:
        #print(full_path, " not found")
        return False
    current_char=read_file(new_file_name)
    if current_char is not None:
        os.rename(new_file_name, new_file_name.replace(".tmp", ""))
        new_file_name = new_file_name.replace(".tmp", "")
        print("File ", new_file_name, " successfully read.")
        return current_char
    else:
        print("File ", new_file_name, " is empty or corrupted.")
        os.remove(new_file_name)
        try:
            remote_command = f"ssh b2webste@biglinux.math.uwaterloo.ca 'rm {full_path}'"
            subprocess.run(remote_command, shell=True, check=True)
            print(f"Remote file {full_path} successfully deleted.")
        except subprocess.CalledProcessError as e:
            print(f"Error deleting remote file {full_path}: {e}")
            return False

def push_to_server(file_name, v_counts):
    local_dir = "/Users/benwebster/b2webste/_binary_" + str(v_counts)
    remote_dir = "b2webste@biglinux.math.uwaterloo.ca:/u/b2webste/b2webste/_binary_" + str(v_counts)
    full_path = remote_dir + "/" + file_name
    new_file_name = local_dir + "/" + file_name
    try:
        command = ["scp", new_file_name, full_path]
        subprocess.run(command, check=True)
        print("File ", new_file_name, " pushed to server.")
    except subprocess.CalledProcessError as e:
        print(f"Error during file transfer: {e}")
        return False

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

def try_to_use_characters(red_good_words, i, n):
    current_char=None
    """Try to use characters of simple modules to compute the character of a standard module"""
    word = red_good_words[i]
    gl_parts, glp_parts = word
    # if all(1 not in part for part in gl_parts) and all(1 not in part for part in glp_parts):
    #     print(f"All parts of {concatenate_word(word)} do not contain 1, using standard character.")
    #     smaller_glp_parts = [[x - 1 for x in part] for part in glp_parts]
    #     smaller_gl_parts = [[x - 1 for x in part] for part in gl_parts]
    #     smaller_word = (smaller_gl_parts, smaller_glp_parts)
    #     c_word = concatenate_word(smaller_word)
    #     v_count = [c_word.count(i) for i in range(1, n + 1)]
    #     file_handle = f"simple_character_{c_word}_v_counts_{v_count}.pkl"
    #     directory_name = f"_binary_{v_count}"
    #     if not os.path.exists(directory_name):
    #         os.makedirs(directory_name, exist_ok=True)
    #     file_name = os.path.join(directory_name, file_handle)
    #     smaller_char = read_file(file_name)
    #     if smaller_char is not None:
    #         # Add 1 to each entry of each key in smaller_char
    #         shifted_char = {}
    #         for key, value in smaller_char.items():
    #             shifted_key = tuple(x + 1 for x in key)
    #             shifted_char[shifted_key] = value
    #         current_char = shifted_char
    #         return current_char
    if glp_parts != []:
        smaller_glp_parts = glp_parts[0:-1]
        #print(f"gl_parts={gl_parts}, glp_parts={glp_parts}, smaller_glp_parts={smaller_glp_parts}")
        smaller_word = [gl_parts,smaller_glp_parts]
        #print(f"smaller_word={smaller_word}")
        c_word = concatenate_word(smaller_word)
        #print(f"c_word={c_word}")
        time.sleep(1)
        v_count = [c_word.count(i) for i in range(1, n + 1)]
        if all(v_count[i] == 0 for i in range(len(v_count))):
            current_char = compute_standard_character(gl_parts, glp_parts, n)
            return current_char
        file_handle = f"simple_character_{c_word}_v_counts_{v_count}.pkl"
        directory_name = f"_binary_{v_count}"
        if not os.path.exists(directory_name):
            os.makedirs(directory_name, exist_ok=True)
        file_name = os.path.join(directory_name, file_handle)
        smaller_char = read_file(file_name)
        if smaller_char is None:
            smaller_red_good_words = generate_red_good_words(n, v_count, 0)
            j = next((idx for idx, w in enumerate(smaller_red_good_words) if w == smaller_word), None)
            if j is not None:
                try:
                    smaller_char=compute_one_simple_character(smaller_red_good_words, j, n)
                except RuntimeError as e:
                    raise RuntimeError(f"Couldn't compute character for {c_word}, trying later.")
                    #print(f"Couldn't compute character for {c_word}, defaulting to standard character: {e}")
            else:
                raise RuntimeError(f"Couldn't find {c_word} in smaller red-good words, trying later.")
                #current_char = compute_standard_character(gl_parts, glp_parts, n)
        if smaller_char is not None:
            current_char = shuffle_dicts(smaller_char, dict_from_word(glp_parts[-1]), n)
        else:
            raise RuntimeError(f"File {file_name} not found or empty, trying again some other time.")
            # print(f"Couldn't read character for {c_word}, defaulting to standard character")
            # current_char = compute_standard_character(gl_parts, glp_parts, n)
    else:
        # Separate gl_parts into two lists: gl_parts_main and gl_parts_tail
        if gl_parts:
            # Find the index where the tail of consecutive equal elements starts
            tail_start = len(gl_parts)
            for idx in range(len(gl_parts) - 1, 0, -1):
                if gl_parts[idx] != gl_parts[idx - 1]:
                    tail_start = idx
                    break
            gl_parts_main = gl_parts[:tail_start]
            gl_parts_tail = gl_parts[tail_start:]
        else:
            gl_parts_main = []
            gl_parts_tail = []
        if gl_parts_main == [] or gl_parts_tail == []:
            return compute_standard_character(gl_parts, glp_parts, n)
        c_word = concatenate_word((gl_parts_main, []))
        v_count = [c_word.count(i) for i in range(1, n + 1)]
        file_handle = f"simple_character_{c_word}_v_counts_{v_count}.pkl"
        directory_name = f"_binary_{v_count}"
        if not os.path.exists(directory_name):
            os.makedirs(directory_name, exist_ok=True)
        file_name = os.path.join(directory_name, file_handle)
        smaller_char = None
        tail_char = None
        smaller_char = read_file(file_name)
        c_word_tail = concatenate_word((gl_parts_tail,[]))
        v_count_tail = [c_word_tail.count(i) for i in range(1, n + 1)]
        tail_handle = f"simple_character_{c_word_tail}_v_counts_{v_count_tail}.pkl"
        tail_directory_name = f"_binary_{v_count_tail}"
        tail_file_name = os.path.join(tail_directory_name, tail_handle)
        if not os.path.exists(tail_directory_name):
            os.makedirs(tail_directory_name)
        if os.path.exists(tail_file_name):
            tail_char = read_file(tail_file_name)
        if tail_char is None:
            #return compute_standard_character(gl_parts_tail, [], n)
            raise RuntimeError(f"File {tail_file_name} not found or empty, trying again some other time.")
        if smaller_char is None:
            smaller_red_good_words = generate_red_good_words(n, v_count, 0)
            j = next((idx for idx, w in enumerate(smaller_red_good_words) if w == (gl_parts_main, [])), None)
            if j is not None:
                try:
                    smaller_char=compute_one_simple_character(smaller_red_good_words, j, n)
                except RuntimeError as e:
                    #print(f"Couldn't compute character for {c_word}, defaulting to standard character: {e}")
                    raise RuntimeError(f"Couldn't compute character for {c_word}, trying later.")
            else:
                #print(f"Couldn't find {c_word} in smaller red-good words, defaulting to standard character")
                #current_char = compute_standard_character(gl_parts, glp_parts, n)
                raise RuntimeError(f"Couldn't find {c_word} in smaller red-good words, trying later.")
        if smaller_char is not None:
            current_char = shuffle_dicts(smaller_char, tail_char, n)
        if current_char is None:
            raise RuntimeError(f"File {file_name} not found or empty, trying again some other time.")
            #current_char = compute_standard_character(gl_parts, glp_parts, n)
    return current_char

def closer_to_a_simple(current_char, red_good_words, n):
    """Check if a character is closer to a simple character than a standard character"""
    for i in range(len(red_good_words) - 1, -1, -1):
        word = red_good_words[i]
        c_word = concatenate_word(word)
        v_count = [c_word.count(i) for i in range(1, n + 1)]
        if c_word not in current_char:
            continue
        if not is_bar_invariant(current_char[c_word]):
            file_handle = f"simple_character_{c_word}_v_counts_{v_count}.pkl"
            directory_name = f"_binary_{v_count}"
            file_name = os.path.join(directory_name, file_handle)

            if not os.path.exists(file_name):
                #print(f"File {file_name} not found. Retrying...")
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
                if wordies not in current_char:
                    current_char[wordies] = LaurentPolynomial()
                current_char[wordies] = current_char[wordies] + (-simple_mult * lower_char[wordies])
                if any(coeff < 0 for coeff in current_char[wordies].coeffs.values()):
                    raise ValueError("These coefficients are supposed to be non-negative")
            return current_char
    return current_char

def closer_for_many_simples(current_chars, red_good_words, n,i):
    if current_chars == dict():
        return dict()
    word = red_good_words[i]
    c_word = concatenate_word(word)
    v_count = [c_word.count(i) for i in range(1, n + 1)]
    bar_invariants = {k: is_bar_invariant(current_chars[k][c_word]) for k in current_chars}
    if any(not bar_invariants[k] for k in bar_invariants.keys()):
        file_handle = f"simple_character_{c_word}_v_counts_{v_count}.pkl"
        directory_name = f"_binary_{v_count}"
        file_name = os.path.join(directory_name, file_handle)

        lower_char = read_file(file_name)
        if lower_char is None:
            #lower_char = check_for_file(file_handle, v_count)
            #if lower_char is None:
                iter_over = list(current_chars.keys())
                for k in iter_over:
                    if not bar_invariants[k]:
                        word = red_good_words[i]
                        wordie = concatenate_word(word)
                        tmp_file_handle = f"tmp_simple_character_{wordie}_v_counts_{v_count}.pkl"
                        tmp_file_name = os.path.join(directory_name, tmp_file_handle)
                        P=Process(target=write_file, args=(tmp_file_name, current_chars[k]))
                        P.start()
                        del current_chars[k]
                        print("removing ", k, " from current_chars")
        else:
            iter_over = list(current_chars.keys())
            for k in iter_over:
                current_char = current_chars[k]
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
                    print("removing", i, "from", k)
                for wordies in lower_char.keys():
                    print("current_char[wordies]=", current_char[wordies], ", simple_mult=", simple_mult, ", lower_char[wordies]=", lower_char[wordies])
                    current_char[wordies] = current_char[wordies] + (-simple_mult * lower_char[wordies])
                    if any(coeff < 0 for coeff in current_char[wordies].coeffs.values()):
                        raise ValueError("These coefficients are supposed to be non-negative")
        print("currently doing", current_chars.keys())
        return current_chars
    return current_chars

def compute_one_simple_character(red_good_words, i, n, noreturn=False):
    """Compute the character of a simple module with progress tracking."""

    word = red_good_words[i]
    gl_parts, glp_parts = word
    wordie = concatenate_word(word)
    print(f"computing for {i} for {wordie},  time={time.strftime('%H:%M:%S', time.localtime())}", flush=True)
    v_count = [wordie.count(i) for i in range(1, n + 1)]
    file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
    tmp_file_handle = f"tmp_simple_character_{wordie}_v_counts_{v_count}.pkl"
    directory_name = f"_binary_{v_count}"
    file_name = os.path.join(directory_name, file_handle)

    if not os.path.exists(directory_name):
        os.makedirs(directory_name, exist_ok=True)

    current_char = read_file(file_name)
    if current_char is not None:
        return current_char

    tmp_file_name = os.path.join(directory_name, tmp_file_handle)
    if os.path.exists(tmp_file_name):
        current_char = read_file(tmp_file_name)
    if current_char is None or not os.path.exists(tmp_file_name):
        current_char = try_to_use_characters(red_good_words, i, n)
        write_file(tmp_file_name, current_char)
    if current_char is None:
        print(f"Standard character for {wordie} not found, computing standard character.")
        current_char = compute_standard_character(gl_parts, glp_parts, n)
    
    
    r=0
    start_time = time.time()
    print_time = time.time() 
    skip = -1
    for j in range(i, -1, -1):
        maybe_char = read_file(file_name)
        if maybe_char is not None:
            return maybe_char
        #queue.put((i, j))
        skip += 1
        if r >400 or (time.time() - start_time) >= 600:
            start_time = time.time() 
            print("saving simple character for ", i, "r=", r,time.strftime("%H:%M:%S", time.localtime()), flush=True)
            P=Process(target=write_file, args=(tmp_file_name, current_char))
            P.start()
            r=1
        lower_word = red_good_words[j]
        lower_wordies = concatenate_word(lower_word)
        if lower_wordies in current_char and not is_bar_invariant(current_char[lower_wordies]):
            print(i, " minus ", j, " skip ", skip,  " r=", r, "since save", int(time.time() - start_time), time.strftime("%H:%M:%S", time.localtime()))
            skip=0
            r+=1
            #print(i, " minus ", j, " ", lower_wordies, "r=", r, "time since last save", int(time.time() - start_time))
            current_char = closer_to_a_simple(current_char, red_good_words, n)
    write_file(file_name, current_char)
    print("finished with", i, wordie, " time=", time.strftime("%H:%M:%S", time.localtime()), flush=True)
    if noreturn:
        return None
    return current_char

def compute_simple_characters(standard_chars,red_good_words):
    #set_memory_limit(500 * 1024 * 1024) 
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
    return "\n".join(f"{word}: {oneify(char[word])}" for word in sorted(char.keys()) if oneify(char[word]) != 0)


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
    tmp_file_name = file_name + ".tmp"
    with open(tmp_file_name, "wb") as file:  # Use "wb" for writing binary files
        pickle.dump(data, file)  # Serialize the data
    os.rename(tmp_file_name, file_name)  # Rename the temporary file to the original name
    #print(file_name, "saved", time.strftime("%H:%M:%S", time.localtime()))


def main_parallel(n, v_counts, skip = 1000, semnum = 10):
    red_good_words = generate_red_good_words(n, v_counts, 0)
    if red_good_words is []:
        return True
    if len(red_good_words) < 15:
        return main(n,v_counts)
    unique_values = {}
    j=0
    not_done = []

    # with ProcessPoolExecutor(max_workers=semnum) as executor:
    #     readings=[]
    for i in range(len(red_good_words)):
        word = red_good_words[i]
        wordie = concatenate_word(word)
        v_count = [wordie.count(i) for i in range(1, n + 1)]
        file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"  # Use .pkl for binary files
        char_file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
        directory_name = f"_binary_{v_count}"
        if not os.path.exists(directory_name):
            os.makedirs(directory_name, exist_ok=True)
        file_name = os.path.join(directory_name, file_handle)
        char_file_name = os.path.join(directory_name, char_file_handle)
        if not os.path.exists(char_file_name):
            #print("File ", file_name, " not found. Can I make it from ", char_file_name, "?")
            not_done.append(i)
        # for i, future in readings:
        #     try:
        #         unique_values[i] = find_dimensions(future.result())
        #         print("File ", char_file_name, " read.)
        #         write_file(os.path.join(directory_name, f"unique_values_{concatenate_word(red_good_words[i])}_v_counts_{v_counts}.pkl"), unique_values[i])
        #     except Exception as e:
        #         print(f"Error reading file {char_file_name}: {e}")
        #         not_done.append(i)

    if not_done == []:
        print("All characters already computed!")
        return True
    print(f"----------------restarting {v_counts}----------------")
    doing= not_done[:skip]
    print(f"doing={doing}")
    print(f"still waiting on {not_done[skip:]}")
    time.sleep(3)
    failed = []
    with ProcessPoolExecutor(max_workers=semnum) as executor:
        # Submit tasks and keep track of (i, future) pairs
        futures = [(i, executor.submit(compute_one_simple_character, red_good_words, i, n, True)) for i in doing]
        for i,future in futures:
            try:
                #print("doing ", i, "th red-good-word:", wordie, flush=True)
                future.result()
                doing.remove(i)
                print(f"doing={doing}", flush=True)
                print(f"all done with {i}  time=", time.strftime("%H:%M:%S", time.localtime()), flush=True)
            # word = red_good_words[i]
            # wordie = concatenate_word(word)
            #print("doing ", i, "th red-good-word:", wordie)
            # try:
            #     file_handle = f"unique_values_{wordie}_v_counts_{v_counts}.pkl"
            #     directory_name = f"_binary_{v_counts}"
            #     file_name = os.path.join(directory_name, file_handle)
            #     #if not os.path.exists(file_name):
            #     unique_values[i] = find_dimensions(future.result())
            #     write_file(file_name, unique_values[i])  # Use write_file
            #     print(f"written vals  {i}")
            #     #print(f"done computing unique values for {i}th word=", wordie)
            except Exception as e:
                doing.remove(i)
                failed.append(i)
                print(f"Still doing={doing}", flush=True)
                print(f"Failed={failed}", flush=True)
                print(f"Error processing {i}th word=", wordie, flush=True)
    print("All done!")
    return False

def main(n, v_counts, skip=0):
    """Main function to compute all characters"""
    print(f"Computing characters for n={n} with counts {v_counts}")
    red_good_words = generate_red_good_words(n, v_counts, 0)
    if red_good_words is []:
        return True
    unique_values = {}
    j=0
    for i in range(skip, len(red_good_words)):
        word = red_good_words[i]
        wordie = concatenate_word(word)
        v_count = [wordie.count(i) for i in range(1, n + 1)]
        file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"
        char_file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
        directory_name = f"_binary_{v_count}"
        file_name = os.path.join(directory_name, file_handle)
        char_file_name = os.path.join(directory_name, char_file_handle)
        if not os.path.exists(char_file_name):
            break
        else: j=i+1
    print("j=",j)
    if j == len(red_good_words):
        return True
    #for i in range(j, len(red_good_words)):
    word = red_good_words[j]
    wordie = concatenate_word(word)
    v_count = [wordie.count(i) for i in range(1, n + 1)]
    # file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"
    # directory_name = f"_binary_{v_count}"
    # file_name = os.path.join(directory_name, file_handle)

    # if not os.path.exists(directory_name):
    #     os.makedirs(directory_name, exist_ok=True)

    print("doing ", j, "th red-good-word:", wordie)
    with Progress() as progress:
        task_ids = {}
        with Manager() as manager:  # Use Manager to create a shared queue
            queue = manager.Queue()
            # task_id = progress.add_task(f"[cyan]Processing word {j}", total=j, visible=True)
            # task_ids[j] = task_id
            #progress.add_task(f"[cyan]Processing word {j}", total=j, visible=True)
            #asyncio.create_task(monitor_progress(queue, progress, task_ids))
            try:
                compute_one_simple_character(red_good_words, j, n,queue)
                print("done computing values for ", concatenate_word(red_good_words[j]))
            except Exception as e:
                print(f"Didn't work to process {file_name}, guess I'll try again: {e}")
                raise RuntimeError(f"Error processing {file_name}: {e}")

    # full_unique_values = set(x for i in range(len(red_good_words)) for x in unique_values[i])
    # print("\nUnique values of characters:")
    # values = [str(value) + " = " + str(value.evaluate_at_q1()) for value in full_unique_values if isinstance(value, LaurentPolynomial)] + \
    #          [str(value) for value in full_unique_values if not isinstance(value, LaurentPolynomial)]
    # print("\n".join(values))

    # file_name = f"results_{n}_vcounts_{v_counts}.pkl"
    # write_file(file_name, full_unique_values)
   
    print("On to the next one!")
    return False
    

def skip_to(n, j, v_counts):
    """Skip to a specific index in the computation"""
    red_good_words = generate_red_good_words(n, v_counts, 0)
    word = red_good_words[j]
    wordie = concatenate_word(word)
    file_handle = f"unique_values_{wordie}_v_counts_{v_counts}.pkl"
    directory_name = f"_binary_{v_counts}"
    file_name = os.path.join(directory_name, file_handle)
    unique_values={}
    if not os.path.exists(directory_name):
        os.makedirs(directory_name, exist_ok=True)
    for i in range(j, len(red_good_words)):
        word = red_good_words[i]
        wordie = concatenate_word(word)
        print("doing ", i, "th red-good-word:", wordie)
        try:
            unique_values[i] = find_dimensions(compute_one_simple_character(red_good_words, i, n))
            print("done computing unique values for ", wordie)
            write_file(file_name, unique_values[i])
            print("wrote unique values for ", wordie)
        except Exception as e:
            print(f"Didn't work to process {file_name}, guess I'll try again: {e}")
def latexify(g):
    if isinstance(g, LaurentPolynomial):
        return g.latex()
    else:
        return str(g)
def oneify(g):
    if isinstance(g, LaurentPolynomial):
        return g.evaluate_at_q1()
    else:
        try:
            m=int(g)
            return m
        except:
            print("I'm not happy", g, "has type", type(g))
            raise ValueError(f"this one is bad")
from sympy import factorint

def return_power(prime,exp):
    if exp==1:
        return f"{prime}"
    else:
        return f"{prime}^{exp}" 

def display_factors(k):
    fact = str(k)+" = "
    dict = factorint(k)

    fact += " \cdot ".join(return_power(prime,exp) for prime, exp in dict.items())+"\n"
    return fact

import matplotlib.pyplot as plt

def sort_unique_values(input):
        i,sub_file_name,char_file_name,red_good_words,n = input
        unique_values_list = read_file(sub_file_name)
        if unique_values_list is None: 
            if os.path.exists(char_file_name):
                unique_values_list = find_dimensions(compute_one_simple_character(red_good_words, i, n))
                write_file(sub_file_name, unique_values_list)  # Use write_file
                print("wrote unique values for word", i)
            else: 
                unique_values_list = {}
        try: 
            unique_values_list = sorted(unique_values_list, key=oneify)
        except Exception as e:
            print(f"Error processing {i}, let's try again: {e}")
            if os.path.exists(char_file_name):
                unique_values_list = find_dimensions(compute_one_simple_character(red_good_words, i, n))
                print(f"{i}: ", str(unique_values_list))
                write_file(sub_file_name, unique_values_list)  # Use write_file
                print("wrote unique values for word", i)
            else:
                unique_values_list = {}
            unique_values_list = sorted(unique_values_list, key=oneify)
        return i, unique_values_list
  

def print_character(n, v_count, red_good_words,i):
    """Print the character for a specific word"""
    word = red_good_words[i]
    c_word = concatenate_word(word)
    v_count = [c_word.count(i) for i in range(1, n + 1)]
    file_handle = f"simple_character_{c_word}_v_counts_{v_count}.pkl"
    directory_name = f"_binary_{v_count}"
    file_name = os.path.join(directory_name, file_handle)
    
    current_char = read_file(file_name)
    if current_char is not None:
        print(f"Character for {c_word}:")
        print(format_character(current_char))

def print_unique_values(n, v_count):
    red_good_words = generate_red_good_words(n, v_count, 0)
    unique_values = {}
    values = {}
    valuesq = {}
    maxes ={}

    file_name = f"results_{n}_vcounts_{v_count}.pkl"
    futures = []     
    full_unique_values = set()
    full_values = set()
    with ProcessPoolExecutor(max_workers=30) as executor:
        for i in range(len(red_good_words)):
            word = red_good_words[i]
            wordie = concatenate_word(word)
            sub_file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"
            directory_name = f"_binary_{v_count}"
            sub_file_name = os.path.join(directory_name, sub_file_handle)
            char_file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
            char_file_name = os.path.join(directory_name, char_file_handle)
            futures.append(executor.submit(sort_unique_values,(i,sub_file_name,char_file_name,red_good_words,n)))
        for i, future in enumerate(futures):
            print(f"trying with {i}")
            try:
                i, unique_values[i] = future.result()
                valuesq[i] = map(latexify, unique_values[i])
                values[i] = map(oneify, unique_values[i])
                maxes[i] = max(values[i])
                for value in unique_values[i]:
                    if value not in full_unique_values:
                        print(f"Unique value for {i}th red-good-word: {wordie}: {oneify(value)}")
                        print_character(n, v_count, red_good_words,i)
                        full_unique_values.add(value)
                        full_values.add(oneify(value))
            except Exception as e:
                print(f"Error processing {i}: {e}")
                unique_values[i] = {}


        # outs = f"Unique dimensions for {i}th red-good-word: {wordie}\n")
        # outs += "\n".join(str(value) for value in values[i]) + "\n"
        # outs += f"Graded dimensions for {i}th red-good-word: {wordie}\n"
        # outs += "\n".join(value for value in valuesq[i]) + "\n"
        # print(outs)
        # with open(file_name, "w") as f:
        #     f.write(outs)
    full_unique_values = sorted(full_unique_values, key=oneify)

    full_values = map(oneify, full_unique_values)
    full_values = sorted(set(full_values), key=oneify)
    full_valuesq = map(latexify, full_unique_values)

    plt.hist(maxes.values(), bins=100)
    plt.xlabel("Max value")
    plt.ylabel("Number of simples")
    plt.title("Histogram of maximum values of simple characters")
    plt.savefig(f"histogram_max_values_{n}_vcounts_{v_count}.png")
    plt.close()

    outs = "\nUnique values of characters:\n"
    outs += ", ".join(display_factors(value) for value in full_values) + "\n"
    outs += "\nGraded values of characters:\n"
    outs += ", ".join(value for value in full_valuesq) + "\n"
    print(outs)
    with open(file_name, "w") as f:
        f.write(outs)
    

    print("All done!")
def find_GK_dimension(n, current_char):
    GKdim=0
    for wordies in current_char.keys():
        first_n_index = next((i for i, x in enumerate(wordies) if x == n), None)
        last_n_index = next((i for i, x in enumerate(reversed(wordies)) if x == n), None)
        if current_char[wordies].coeffs[0] != 0:
            last_n_index = len(wordies) - 1 - last_n_index
            before_count = first_n_index
            after_count = len(wordies) - last_n_index - 1
            if before_count + after_count > GKdim:
                #print("wordies=",wordies,"gives ", before_count + after_count, " GKdim=", GKdim)
                GKdim = before_count + after_count
    return GKdim

def infinite_weight_space(n, current_char):
    IWS = False
    for wordies in current_char.keys():
        first_n_index = next((i for i, x in enumerate(wordies) if x == n), None)
        last_n_index = next((i for i, x in enumerate(reversed(wordies)) if x == n), None)
        if current_char[wordies].coeffs[0] != 0:
            last_n_index = len(wordies) - 1 - last_n_index
            before_n = wordies[:first_n_index]
            after_n = wordies[last_n_index + 1:]
            if any(x in after_n for x in before_n):
                IWS = True
            break
    return IWS

def redundant_word(word):
    for i in range(len(word) - 1):
        if word[i] < word[i + 1] - 1:
            return True
    return False

def process_character_file(red_good_words, i, n, done_chars, find_dim=False):
    import time
    start_time = time.time()
    
    word = red_good_words[i]
    wordie = concatenate_word(word)
    v_count = [wordie.count(i) for i in range(1, n + 1)]
    directory_name = f"_binary_{v_count}"
    char_file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
    char_file_name = os.path.join(directory_name, char_file_handle)
    
    # Quick check if file exists before trying to read
    if not os.path.exists(char_file_name):
        return None
    
    current_char = read_file(char_file_name)
    if current_char is None:
        return None
        
    # Pre-filter working words for efficiency
    current_working_words = [wordies for wordies in current_char.keys() 
                           if not redundant_word(wordies) and wordies not in done_chars]
    
    if find_dim:
        GKdim = find_GK_dimension(n, current_char)
        IWS = infinite_weight_space(n, current_char)
        elapsed = time.time() - start_time
        #if elapsed > 0.1:  # Only print for slow operations
        print(f"Processed {i} ({wordie}) in {elapsed:.3f}s - GKdim: {GKdim}, IWS: {IWS}")
        return current_char, current_working_words, GKdim, IWS
    else: 
        #if elapsed > 0.1:  # Only print for slow operations
            #print(f"Processed {i} ({wordie}) in {elapsed:.3f}s")
        return current_char

from concurrent.futures import as_completed

def print_simple_dimensions(n, v_count, rnge=1, semnum=20):
    import time
    import psutil
    
    print(f"Starting with {semnum} workers, batch size {rnge}")
    print(f"System has {psutil.cpu_count(logical=False)} physical cores, {psutil.cpu_count(logical=True)} logical cores")
    
    red_good_words = generate_red_good_words(n, v_count, 0)
    print(f"Total red_good_words: {len(red_good_words)}")
    
    unique_values = {}
    values = {}
    valuesq = {}
    maxes = {}

    file_handle = f"results_{n}_vcounts_{v_count}.pkl"
    last_word_handle = f"last_word_{n}_vcounts_{v_count}.pkl"
    directory_name = f"_binary_{v_count}"
    file_name = os.path.join(directory_name, file_handle)
    last_word_name = os.path.join(directory_name, last_word_handle)
    if os.path.exists(last_word_name):
        irrep_sizes, done_chars, GKdims, IWS = read_file(last_word_name)
        print("loaded irrep_sizes from ", last_word_name)
        print(irrep_sizes, done_chars, GKdims, IWS)
    if not os.path.exists(last_word_name) or irrep_sizes is None:
        irrep_sizes = set()
        done_chars = []
        GKdims = [None] * len(red_good_words)  # Pre-allocate the list with None
        IWS = [None] * len(red_good_words)    # Pre-allocate the list with None
    reps =int(len(red_good_words)/rnge)
    for i in range(reps):
        working_words = set()
        current_irrep_sizes = dict()
        
        # Phase 1: Process primary batch to get working_words
        batch_start = i * rnge
        batch_end = min((i + 1) * rnge, len(red_good_words))
        primary_jobs = list(range(batch_start, batch_end))
        
        print(f"Batch {i}: Processing {len(primary_jobs)} primary jobs in parallel")
        start_time = time.time()
        
        with ProcessPoolExecutor(max_workers=semnum) as executor:
            # Submit primary batch jobs in parallel
            futures1 = {}
            for j in primary_jobs:
                future = executor.submit(process_character_file, red_good_words, j, n, done_chars, True)
                futures1[future] = j
            
            # Process primary results as they complete
            completed_primary = 0
            for future in as_completed(futures1):
                j = futures1[future]
                result = future.result()
                completed_primary += 1
                
                if completed_primary % 5 == 0:
                    elapsed = time.time() - start_time
                    rate = completed_primary / elapsed if elapsed > 0 else 0
                    print(f"Primary: {completed_primary}/{len(primary_jobs)} ({rate:.1f}/sec) in {elapsed:.1f}s")
                
                if result is None:
                    print(f"Character file for {j} not found, skipping.")
                    continue
                    
                current_char, current_working_words, GKdims[j], IWS[j] = result
                working_words.update(current_working_words)
                
                # Process dimensions for primary batch
                for wordies in working_words:
                    if wordies not in current_char.keys():
                        continue
                    dim = oneify(current_char[wordies])
                    if dim > 0:                        
                        if wordies not in current_irrep_sizes:
                            current_irrep_sizes[wordies] = [dim]
                        else:
                            current_irrep_sizes[wordies].append(dim)
            
            primary_time = time.time() - start_time
            print(f"Primary batch completed in {primary_time:.1f}s, found {len(working_words)} working words")
            
            # Phase 2: Process secondary batch with the working_words from phase 1
            secondary_jobs = list(range(batch_end, len(red_good_words)))
            if secondary_jobs:
                print(f"Processing {len(secondary_jobs)} secondary jobs in parallel")
                secondary_start = time.time()
                
                futures2 = {}
                for j in secondary_jobs:
                    future = executor.submit(process_character_file, red_good_words, j, n, done_chars, False)
                    futures2[future] = j
                
                completed_secondary = 0
                for future in as_completed(futures2):
                    j = futures2[future]
                    result_char = future.result()
                    completed_secondary += 1
                    
                    if completed_secondary % 10 == 0:
                        elapsed = time.time() - secondary_start
                        rate = completed_secondary / elapsed if elapsed > 0 else 0
                        print(f"Secondary: {completed_secondary}/{len(secondary_jobs)} ({rate:.1f}/sec) in {elapsed:.1f}s")
                    
                    if result_char is None:
                        continue
                        
                    for wordies in working_words:
                        if wordies not in result_char.keys():
                            continue
                        dim = oneify(result_char[wordies])
                        if dim > 0:                        
                            if wordies not in current_irrep_sizes:
                                current_irrep_sizes[wordies] = [dim]
                            else:
                                current_irrep_sizes[wordies].append(dim)
                
                secondary_time = time.time() - secondary_start
                print(f"Secondary batch completed in {secondary_time:.1f}s")
            
            total_time = time.time() - start_time
            total_jobs = len(primary_jobs) + len(secondary_jobs)
            print(f"Batch {i} total: {total_jobs} jobs in {total_time:.1f}s ({total_jobs/total_time:.1f} jobs/sec)")
        current_irrep_sizes = {key: sorted(tuple(value)) for key, value in current_irrep_sizes.items()}
        for wordies in working_words:
            if wordies in current_irrep_sizes.keys():
                print("wordies=", wordies, "gives ", current_irrep_sizes[wordies])
                irrep_sizes.add(tuple(current_irrep_sizes[wordies]))
                done_chars.append(wordies)
        write_file(last_word_name, [irrep_sizes, done_chars, GKdims, IWS])
    print(irrep_sizes)
    # gk_dims_true = [GKdims[i] for i in range(len(GKdims)) if IWS[i]]
    # gk_dims_false = [GKdims[i] for i in range(len(GKdims)) if not IWS[i]]
    # maxdim=sum(v_count)-v_count[n-1]
    # plt.hist(
    #     [gk_dims_false, gk_dims_true],
    #     bins=range(maxdim + 2),  # Ensure bins cover the full range of GKdims
    #     align='left',
    #     stacked=True,
    #     color=['blue', 'orange'],  # One color per dataset
    #     label=['IWS', 'No IWS']
    # )

    # # Add legend and labels
    # plt.legend()
    # plt.xlabel("GK dimension")
    # plt.ylabel("Number of simples")
    # plt.title("Histogram of GK dimensions of simple modules")
    # plt.savefig(f"histogram_GK_dims_{n}_vcounts_{v_count}.png")
    # plt.close()

def wordie_file_read(file,v_count,n):
    directory_name = f"_binary_{v_count}"
    subdirectory_handle = f"words"
    subdirectory_name = os.path.join(directory_name, subdirectory_handle)
    # Extract 'wordie' from the filename, assuming the format is 'sizes_{wordie}'
    if file.startswith("sizes_"):
        wordie = file[len("sizes_"):]
        # Optionally, remove file extension if present
        wordie = os.path.splitext(wordie)[0]
        idx,sizes_by_word = read_file(os.path.join(subdirectory_name, file))
        #print(f"Found wordie: {wordie} from file: {file}, starting at idx={idx}")
    return wordie, idx, sizes_by_word

def async_write_progress(index, sizes_by_word_snapshot, GKdims, IWS, GI_file_name, subdirectory_name):
        write_file(GI_file_name, (GKdims, IWS))
        for wordies in sizes_by_word_snapshot.keys():
            wordie_file_handle = f"sizes_{wordies}"
            wordie_file_name = os.path.join(subdirectory_name, wordie_file_handle)
            write_file(wordie_file_name, (index,sizes_by_word_snapshot[wordies]))
        print(f"Done writing characters for idx={index}.")

def sort_irrep_sizes(files):
    irrep_sizes = set()
    for file in files:
        wordie, idx, sizes_by_word = wordie_file_read(file, v_count, n)
        if idx == True:
            sorted_sizes = tuple(sorted(sizes_by_word.values()))
            irrep_sizes.update(sorted_sizes)
    return irrep_sizes

def print_simple_dimensions2(n, v_count, rnge=100, semnum=20, skip=0):
    import time
    import psutil
    
    print(f"Starting with {semnum} workers, batch size {rnge}")
    print(f"System has {psutil.cpu_count(logical=False)} physical cores, {psutil.cpu_count(logical=True)} logical cores")
    
    red_good_words = generate_red_good_words(n, v_count, 0)
    print(f"Total red_good_words: {len(red_good_words)}")
    
    unique_values = {}
    values = {}
    valuesq = {}
    maxes = {}

    file_handle = f"results_{n}_vcounts_{v_count}.pkl"
    done_handle = f"done_{n}_vcounts_{v_count}.pkl"
    directory_name = f"_binary_{v_count}"
    subdirectory_handle = f"words"
    GI_handle = f"GI_{n}_{v_count}.pkl"
    file_name = os.path.join(directory_name, file_handle)
    GI_file_name = os.path.join(directory_name, GI_handle)
    subdirectory_name = os.path.join(directory_name, subdirectory_handle)
    done_name = os.path.join(subdirectory_name,done_handle)
    if not os.path.exists(subdirectory_name):
        os.makedirs(subdirectory_name, exist_ok=True)
    if os.path.exists(GI_file_name):
        GKdims, IWS = read_file(GI_file_name)
    else:
        GKdims = [None] * len(red_good_words) 
        IWS = [None] * len(red_good_words)
    working_words = set()
    current_irrep_sizes = dict()
    start_time = time.time()
    completed_primary = 0
    sizes_by_word = dict()
    idx = dict()
    files = [f for f in os.listdir(subdirectory_name) if os.path.isfile(os.path.join(subdirectory_name, f)) and f.startswith("sizes_")]
  
    for f in files:
        wordie,idx_temp, sizes_by_word_temp = wordie_file_read(f, v_count,n)
        idx[wordie]=idx_temp
        sizes_by_word[wordie]=sizes_by_word_temp
        if idx[wordie] != True:
            working_words.add(wordie)
        if len(list(working_words)) >= semnum:
            break


    if working_words:
        start_idx = min(idx[wordie] for wordie in working_words)
        GK_start = min(idx for idx, val in enumerate(GKdims) if val is None)
        IWS_start = min(idx for idx, val in enumerate(IWS) if val is None)
        start_idx = min(start_idx, GK_start, IWS_start)
    else: 
        irrep_sizes=sort_irrep_sizes(files)
        write_file(file_name,irrep_sizes)
    print(f"Starting from index {start_idx}")
    done_chars=list(range(start_idx))
    futures1=dict()
    left_to_do=list(range(start_idx, len(red_good_words)))
    to_do=len(left_to_do)
    print(f"size of working_words={len(list(working_words))}")
    not_doing_now = left_to_do[rnge:]
    last_time = time.time()
    for j in left_to_do[:rnge]:
        result =process_character_file(red_good_words, j, n, done_chars, True)
        if result is None:
            print(f"Character file for {j} not found, skipping.")
            sizes_by_word_snapshot = sizes_by_word.copy()
            async_write_progress(j-1, sizes_by_word_snapshot, GKdims, IWS, GI_file_name, subdirectory_name)
            return False
        current_char, current_working_words, GKdims[j], IWS[j] = result
        for wordies in current_working_words:
            wordie_file_handle = f"sizes_{wordies}"
            wordie_file_name = os.path.join(subdirectory_name, wordie_file_handle)
            dim = oneify(current_char[wordies])
            if not os.path.exists(wordie_file_name) and dim > 0:
                print(f"Writing {wordies} to {wordie_file_name}")
                write_file(wordie_file_name, (j+1, {j:dim}))
            if len(list(working_words)) < semnum:
                working_words.add(wordies)
            
        
        #working_words.update(current_working_words)
        
        # Process dimensions for primary batch
        for wordies in working_words:
            if wordies not in current_char.keys():
                continue
            dim = oneify(current_char[wordies])
            if dim > 0:                        
                if wordies not in sizes_by_word:
                    sizes_by_word[wordies] = {j: dim}
                else:
                    sizes_by_word[wordies][j] = dim
        done_chars.append(j)
        completed_primary += 1
        since_wrote = time.time() - last_time
        print(f"since_wrote: {since_wrote}, j={j}")
        elapsed = time.time() - start_time
        if since_wrote > 600:
            last_time = time.time()
            rate = completed_primary / elapsed if elapsed > 0 else 0
            print(f"Completed {completed_primary}/{to_do} ({rate:.1f}/sec) in {elapsed:.1f}s.  {since_wrote} seconds since last wrote")
            sizes_by_word_snapshot = sizes_by_word.copy()
            p = multiprocessing.Process(target=async_write_progress, args=(j+1, sizes_by_word_snapshot, GKdims, IWS, GI_file_name,subdirectory_name))
            p.start()
        # Start a separate process to write characters so far, allowing the while loop to continue


    # Take a snapshot of current state to avoid race conditions
    sizes_by_word_snapshot = sizes_by_word.copy()
    if not_doing_now == []:
        index = True
    else:
        index=min(not_doing_now)
    print(f"Writing characters so far for idx={index}")
    p = multiprocessing.Process(target=async_write_progress, args=(index, sizes_by_word_snapshot, GKdims, IWS, GI_file_name,subdirectory_name))
    p.start()
    
    return False
                

    # for wordies in sizes_by_word.keys():
    #     current_irrep_sizes = sorted(tuple(sizes_by_word[wordies].values()))
    #     irrep_sizes.add(current_irrep_sizes)
    # write_file(file_name, [irrep_sizes, done_chars, GKdims, IWS])

    #print(irrep_sizes)


import asyncio
import threading
from itertools import product
import multiprocessing

def compute_one_character_in_process(inputs):
    """Compute one character in a separate process."""
    red_good_words, i, n, attempt,queue = inputs
    #print("Computing character in process for ", i, "attempt", attempt)
#    try:
    print(f"Computing character in process for {i} attempt {attempt}")
    return compute_one_simple_character(red_good_words, i, n,queue)
    # except Exception as e:
    #     print(f"Error processing {i}: {e}")
    #     raise ValueError(f"Does having a ValueError help?  File for {i} not found in compute_one_character_in_process. Will try again.")
    #     raise RuntimeError(f"File for {i} not found in compute_one_character_in_process. Will try again.")

def print_semaphore_status(semaphore, label="Semaphore Status"):
    """Print the current state of the semaphore."""
    print(f"{label}: Available permits = {semaphore._value}")

# async def process_word_async_with_throttle(red_good_words, i, n, executor, semaphore,start_time,j,queue,delay):
#     #async with semaphore:  # Limit concurrency
#     # if time.time() - start_time <= 120:
#     #     wait = (i - j) 
#     #     await asyncio.sleep(wait)  # Add 'await' here
#     word = red_good_words[i]
#     wordie = concatenate_word(word)
#     v_count = [wordie.count(i) for i in range(1, n + 1)]
#     file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"
#     char_file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
#     directory_name = f"_binary_{v_count}"
#     file_name = os.path.join(directory_name, file_handle)
#     char_file_name = os.path.join(directory_name, char_file_handle)

#     await asyncio.to_thread(os.makedirs, directory_name, exist_ok=True)

#     if not os.path.exists(char_file_name):
#         current_char = await async_compute_one_simple_character(red_good_words, i, n, executor, semaphore,queue,delay)
#         dimensions = find_dimensions(current_char)
#         await asyncio.to_thread(write_file, file_name, dimensions)
#         print("Wrote unique values for", wordie)
#     else:
#         if os.path.exists(file_name):
#             dimensions = await asyncio.to_thread(read_file, file_name)
#         else:
#             current_char = await asyncio.to_thread(read_file, char_file_name)
#             if current_char is not None:
#                 dimensions = find_dimensions(current_char)
#                 await asyncio.to_thread(write_file, file_name, dimensions)
#             else:
#                 print("File", char_file_name, "is empty or corrupted.")
#     queue.put((i, "done"))
#     print("Done with", i, "th red-good-word:", wordie)

async def monitor_progress(queue, progress, task_ids, not_done,still_running):
    current_tasks = []
    if not_done == set():
        return True  
    # if len(not_done) >10 and len(still_running) < 10:
    #     print("too few tasks running, let's try again")
    #     return False
    while True:
        last_time = time.time()
        try:
            i, j = queue.get_nowait()  # Non-blocking queue read
            # #print(f"receiving queue.put(({i}, {j}))")
            # progress.update(task_ids[i], advance=1)
            # if i > j+20:
            #     progress.update(task_ids[i], visible=True)
            # if j == "failure":
            #     progress.update(task_ids[i], visible=False)
            if j == "done":
                not_done.discard(i)
                still_running.discard(i)
                if time.time() - last_time > 20:
                    print("len(not_done) =", len(not_done) , "len(still_running) = ", len(still_running))
                    print("still_running = ", sorted(list(still_running))[:100])
                if not_done == set():
                    print("All tasks done!")
                    return True
                # if len(not_done) >10 and len(still_running) < 10:
                #     return False
        except Exception:
            await asyncio.sleep(.01)  # Sleep briefly to avoid busy-waiting

async def main_parallel_async(n, v_counts, skip=0,rnge=1000,semnum=20,delay=20):
    """Asynchronous version of main_parallel."""
    red_good_words = generate_red_good_words(n, v_counts, 0)
    if red_good_words is None:
        return True
    if len(red_good_words) == 0:
        return True
    if len(red_good_words) <= 200:
        semnum = min(semnum, int(len(red_good_words)/10+1))
    semaphore = asyncio.Semaphore(semnum) 
    unique_values = {}
    tasks = []
    task_ids = {}
    not_done = set()
    still_running = set()
    j=0
    start_time=time.time()
    with Progress() as progress:
        with Manager() as manager:  # Use Manager to create a shared queue
            queue = manager.Queue()
            mini = 0 
            maxi = 0
            with ProcessPoolExecutor(max_workers=semnum) as executor:
                for i in range(skip,len(red_good_words)):
                    word = red_good_words[i]
                    wordie = concatenate_word(word)
                    v_count = [wordie.count(i) for i in range(1, n + 1)]
                    file_handle = f"unique_values_{wordie}_v_counts_{v_count}.pkl"
                    char_file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
                    directory_name = f"_binary_{v_count}"
                    file_name = os.path.join(directory_name, file_handle)
                    char_file_name = os.path.join(directory_name, char_file_handle)
                    unique_values[i] = read_file(file_name)
                    if not os.path.exists(char_file_name):
                        not_done.add(i)
                        if mini == 0:
                            mini = i
                        if i - mini < rnge:
                            still_running.add(i)
                            task_ids[i] = progress.add_task(f"[cyan]Processing word {i}", total=i, visible=False)
                            tasks.append(
                                async_compute_one_simple_character(red_good_words, i, n, executor, semaphore,queue,delay)
                            )
                    if i > maxi:
                        maxi = i
                if not tasks:
                    print("No tasks to run, all characters already computed.")
                    return True
                #monitor_task = asyncio.create_task(monitor_progress(queue, progress, task_ids, not_done, still_running))
                worker_tasks = asyncio.gather(*tasks, return_exceptions=True)
                await worker_tasks  # Wait for all worker tasks to complete
                # done, pending = await asyncio.wait(
                #     [monitor_task, worker_tasks],
                #     return_when=asyncio.FIRST_COMPLETED,
                # )

                # if monitor_task in done:
                #     monitor_result = monitor_task.result()
                #     print(f"Monitor task returned {monitor_result}.")
                #     return monitor_result

    # Process full unique values if all tasks are completed
    # full_unique_values = set(x for i in range(len(red_good_words)) for x in unique_values.get(i, []))
    # print("\nUnique values of characters:")
    # values = [str(value) + " = " + str(value.evaluate_at_q1()) for value in full_unique_values if isinstance(value, LaurentPolynomial)] + \
    #          [str(value) for value in full_unique_values if not isinstance(value, LaurentPolynomial)]
    # print("\n".join(values))
    # file_name = f"results_{n}_vcounts_{v_counts}.pkl"
    # await asyncio.to_thread(write_file, file_name, full_unique_values)
    print("All done!")
    if maxi == len(red_good_words):
        return True
    else:
        return False

# async def background_task(i):
#         while True:
#             print(f"{i} has a semaphore")
#             await asyncio.sleep(5)

async def async_compute_one_simple_character(red_good_words, i, n, executor, semaphore, queue, retries=3, delay=10):
    """Asynchronous wrapper for compute_one_character_in_process with retry logic."""
    loop = asyncio.get_running_loop()
    attempt = 1
    
    while attempt <= retries:
        start_time = time.time()
        print(f"Attempt {attempt} for word {i}")
        
        if attempt > 1:
            print(f"Waiting {delay} seconds before retry...")
            await asyncio.sleep(delay)
        
        try:
            async with semaphore:  # This properly handles acquire and release
                print(f"Waited {time.time() - start_time} seconds for semaphore")
                print_semaphore_status(semaphore, f"After getting semaphore for word {i}, attempt {attempt}")
                
                result = await loop.run_in_executor(
                    executor, 
                    compute_one_character_in_process, 
                    (red_good_words, i, n, attempt,queue)
                )
                
                print(f"Successfully finished async_compute_one_simple_character on word {i} on attempt {attempt}")
                #queue.put((i, "done"))
                return result
                
        except Exception as e:
            print(f"Attempt {attempt} failed for word {i}: {e}")
            #queue.put((i, "failure"))
            attempt += 1
    return None  # Return None if all attempts fail
    print(f"All attempts failed for word {i}. Giving up after {retries} retries.")
    

def do_many(n, v_counts, skip=0):
    red_good_words = generate_red_good_words(n, v_counts, 0)
    ell=len(red_good_words)-skip
    print("ell=", ell)
    current_chars = dict()
    r=0
    start_time = time.time()
    print_time = time.time() 
    skip = 1
    not_done = set()
    directory_name = f"_binary_{v_counts}"
    if not os.path.exists(directory_name):
        os.makedirs(directory_name, exist_ok=True)
    for i in reversed(range(ell)):
        print("doing ", i)
        current_chars = closer_for_many_simples(current_chars, red_good_words, n,i)
        r+=1
        if (time.time() - start_time) >= 1200: 
            r=1    
            start_time = time.time() 
            print("saving simple character for ", current_chars.keys(), "r=", r,time.strftime("%H:%M:%S", time.localtime()))
            for k in current_chars.keys():
                word = red_good_words[k]
                wordie = concatenate_word(word)
                tmp_file_handle = f"tmp_simple_character_{wordie}_v_counts_{v_count}.pkl"
                tmp_file_name = os.path.join(directory_name, tmp_file_handle)
                current_char = current_chars[k]
                P=Process(target=write_file, args=(tmp_file_name, current_char))
                P.start()
        word = red_good_words[i]
        wordie = concatenate_word(word)
        v_count = [wordie.count(i) for i in range(1, n + 1)]
        char_file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
        char_file_name = os.path.join(directory_name, char_file_handle)
        if not os.path.exists(char_file_name):
            not_done.add(i)
            tmp_file_handle = f"tmp_simple_character_{wordie}_v_counts_{v_count}.pkl"
            tmp_file_name = os.path.join(directory_name, tmp_file_handle)
            if os.path.exists(tmp_file_name):
                current_char = read_file(tmp_file_name)
                print("read temporary character for ", i)
            else:
                current_char = compute_standard_character(word[0], word[1], n)
                write_file(tmp_file_name, current_char)
            if current_char is None:
                current_char = compute_standard_character(word[0], word[1], n)
                write_file(tmp_file_name, current_char)
            current_chars[i] = current_char
    for k in current_chars.keys():
        word = red_good_words[k]
        wordie = concatenate_word(word)
        file_handle = f"simple_character_{wordie}_v_counts_{v_count}.pkl"
        file_name = os.path.join(directory_name, file_handle)
        current_char = current_chars[k]
        write_file(file_name, current_char)
        print("wrote simple character for ", k, time.strftime("%H:%M:%S", time.localtime()))
        time.sleep(3)
    if skip == 0 and not_done==set():
        print("All done!")
        return True
    else:
        print("On to the next one!")
        return False

def all_smaller_vcounts(vcounts):
    result=[]
    for i in range(vcounts[-1]+1):
        #print(f"vcounts= {vcounts}, i = {i}, result = {result}")
        if len(vcounts) == 1:
            result.append([i])
        else:
            partial_result = all_smaller_vcounts(vcounts[:-1])
            for smaller_vcounts in partial_result:
                result.append(smaller_vcounts+[i])
    return result

# To run the async main_parallel_async function
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Compute characters of simple modules.")
    parser.add_argument("mode", choices=["main", "main_parallel", "main_parallel_async", "print_unique_values", "print_sd", "skip_to","do_many"], help="Mode to run the script in.")
    parser.add_argument("n", type=int, help="Value of n.")
    parser.add_argument("v_counts", type=int, nargs="+", help="List of counts.")
    parser.add_argument("--skip", type=int, default=0, help="Index to skip to in the computation.")
    parser.add_argument("--rnge", type=int, default=1000, help="Range to cover in the computation.")
    parser.add_argument("--semnum", type=int, default=10, help="Number of semaphores to use.")
    parser.add_argument("--delay", type=int, default=60, help="Delay before retrying.")
    args = parser.parse_args()


    if args.mode == "print_unique_values":
        print_unique_values(args.n, args.v_counts)
    elif args.mode == "print_sd":
        done = False
        while done == False:
            done=print_simple_dimensions2(args.n, args.v_counts,args.rnge,args.semnum,args.skip)
    else:
        done = False
        while done == False:
            if args.mode == "main_parallel_async":
                done = asyncio.run(main_parallel_async(args.n, args.v_counts, args.skip,args.rnge,args.semnum,args.delay))
                args.rnge = args.rnge +10
            elif args.mode == "main_parallel":
                main_parallel(args.n, args.v_counts)
            elif args.mode == "main":
                done = main(args.n, args.v_counts,args.skip)
            elif args.mode == "skip_to":
                skip_to(args.n, args.skip, args.v_counts)
            elif args.mode == "do_many":
                for smaller_vcounts in all_smaller_vcounts(args.v_counts):
                    if smaller_vcounts[-1] != 0 and any(args.v_counts[i]-smaller_vcounts[i] > args.v_counts[i+1]-smaller_vcounts[i+1] for i in range(len(smaller_vcounts)-1)):
                        print("skipping ", smaller_vcounts)
                        continue
                
                    sub_done = False
                    while sub_done == False:
                        print(f"Running {smaller_vcounts}.")
                        sub_done = main_parallel(args.n, smaller_vcounts, args.rnge,args.semnum)
                
