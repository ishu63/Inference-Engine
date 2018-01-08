import re
import copy
import sys

sys.setrecursionlimit(100000)


def index_2d(myList, v):
    for i, x in enumerate(myList):
        if v in x:
            return (i, x.index(v))
    return False


def standardize(stmt1, stmt2):
    dict = {}
    i = 0
    for list in stmt1:
        j = 1
        for var in list[2:]:
            j += 1
            if not type(var) == int:
                if not var[0].isupper():
                    if var not in dict:
                        i += 1
                        dict[var] = i
                        list[j] = i
                    else:
                        list[j] = dict.get(var)
            else:
                if var not in dict:
                    i += 1
                    dict[var] = i
                    list[j] = i
                else:
                    list[j] = dict.get(var)
    dict = {}
    for list in stmt2:
        j = 1
        for var in list[2:]:
            j += 1
            if not type(var) == int:
                if not var.istitle():
                    if var not in dict:
                        i += 1
                        dict[var] = i
                        list[j] = i
                    else:
                        list[j] = dict.get(var)
            else:
                if var not in dict:
                    i += 1
                    dict[var] = i
                    list[j] = i
                else:
                    list[j] = dict.get(var)


def unifystmt(stmt1, stmt2):
    if len(stmt1) == len(stmt2) == 1:   # both have only one predicate left
        aaa = [isinstance(x, int) for x in stmt1[2:]]
        aaaa = [isinstance(x, int) for x in stmt2[2:]]
        aaa.extend(aaaa)
        if False in aaa:#aanot any(isinstance(x, int) for x in stmt1[2:]):
            #if False in aaaa:#not any(isinstance(x, int) for x in stmt2[2:]):
            if stmt1[0][1] == stmt2[0][1]:
                for i in range(2,len(stmt1[0])):
                    if not stmt1[0][i] == stmt2[0][i]:
                        return False  # some predicate did not match
                return True   # all predicates matched
            return False   # both predicates are different
    standardize(stmt1, stmt2)
    unificated_list = {}
    list1 = stmt1[0]
    flag = 0
    for list2 in stmt2:
        if (list1[1] == list2[1] and (not list1[0] == list2[0])):
            for i in range(2,len(list1)):
                if (isinstance(list1[i], int) and (not isinstance(list2[i], int))):
                    unificated_list[list1[i]] = list2[i]
                elif (not isinstance(list1[i], int) and (isinstance(list2[i], int))):
                    unificated_list[list2[i]] = list1[i]
                elif (isinstance(list1[i], int) and (isinstance(list2[i], int))):
                    unificated_list[list2[i]] = list1[i]
                # add condition when both are Constant but they are different so can't unify
                elif (not isinstance(list1[i], int) and (not isinstance(list2[i], int))):
                    if not list1[i] == list2[i]:
                        unificated_list.clear()
                        return False
                    else:
                        flag += 1
    if len(unificated_list)==0 and flag == len(stmt1[0])-2 and len(stmt1)==len(stmt2)==1:
        return True
    resolved_stmt1 = copy.deepcopy(stmt1[1:])
    resolved_stmt2 = copy.deepcopy(stmt2)
    remove_dict = {'l1': [-1] ,'l2': [-1] }
    j = -1
    for list1 in resolved_stmt1:
        j += 1
        k = -1
        for list2 in resolved_stmt2:
            k += 1
            if (not list1[0] == list2[0]) and (list1[1] == list2[1]):
                for i in range(2,len(list1)):
                    if (not (isinstance(list1[i], int) and (isinstance(list2[i], int)))):
                        break
                    else:
                        # remove that predicate from both lists
                        remove_dict['l1'].append(j)
                        remove_dict['l2'].append(k)
    remove_dict['l1'].remove(-1)
    remove_dict['l2'].remove(-1)
    l11 = sorted(remove_dict['l1'], reverse=True)
    l22 = sorted(remove_dict['l2'], reverse=True)
    l1 = l11[::-1]
    l2 = l22[::-1]
    if l1:
        for i in l1:
            del resolved_stmt1[i]
    if l2:
        for i in l2:
            del resolved_stmt2[i]
    for list in resolved_stmt2:
        if (list[1] == stmt1[0][1] and (not list[0] == stmt1[0][0])):
            resolved_stmt2.remove(list)
            break
    resolved_stmt1.extend(resolved_stmt2)
    if len(resolved_stmt1) == 0:
        return True
    if not len(unificated_list) == 0:
        for list in resolved_stmt1:
            i = 1
            for item in list[2:]:
                i += 1
                if unificated_list.has_key(item):
                    list[i] = unificated_list.get(item)
    if not resolved_stmt1 in intermediate_result:
        intermediate_result.append(resolved_stmt1)
    else:
        return
    if resolved_stmt1[0][0] == '~':
        place = index_2d(positive_index_table, resolved_stmt1[0][1])
        if place:
            for item in positive_index_table[place[0]][1:]:
                stmt = copy.deepcopy(KB[item])
                value = unifystmt(resolved_stmt1, stmt)   # unify query with + stmt in KB
                if value == True:
                    return True
        else:
            return False
    else:
        place = index_2d(negative_index_table, resolved_stmt1[0][1])
        if place:
            for item in negative_index_table[place[0]][1:]:
                stmt = copy.deepcopy(KB[item])
                value = unifystmt(resolved_stmt1, stmt)   # unify query with - stmt in KB
                if value == True:
                    return True
        else:
            return False
    return False


def unify(stmt, query):
    resolved_stmt = copy.deepcopy(stmt)
    for list in stmt:
        if list[1] == query[1] and list[0] == query[0]:
            i=1
            unificated_list = {}
            for element in list[2:]:
                i = i+1
                if element.islower() and query[i][0].isupper():
                    unificated_list[element] = query[i]
            resolved_stmt.remove(list)
    if len(resolved_stmt) == 0:
        return True
    for list in resolved_stmt:
        i = 1
        for item in list[2:]:
            i += 1
            if unificated_list.has_key(item):
                list[i] = unificated_list.get(item)
    if not resolved_stmt in intermediate_result:
        intermediate_result.append(resolved_stmt)
    else:
        return
    if resolved_stmt[0][0] == '~':
        place = index_2d(positive_index_table, resolved_stmt[0][1])
        if place:
            for item in positive_index_table[place[0]][1:]:
                stmt = copy.deepcopy(KB[item])
                value = unifystmt(resolved_stmt, stmt)   # unify query with + stmt in KB
                if value == True:
                    return True
        else:
            return False
    else:
        place = index_2d(negative_index_table, resolved_stmt[0][1])
        if place:
            for item in negative_index_table[place[0]][1:]:
                stmt = copy.deepcopy(KB[item])
                value = unifystmt(resolved_stmt, stmt)   # unify query with - stmt in KB
                if value == True:
                    return True
        else:
            return False
    return False


inputfile = open("input.txt", "r")
outputfile = open("output.txt", "w")

no_query = int(inputfile.readline())
queries = []   # 2D list for storing queries
for i in range(no_query):
    lst = []
    x = inputfile.tell()
    chr = inputfile.read(1)
    if chr == '~':
        lst.append('~')
    else:
        lst.append(' ')
        inputfile.seek(x)
    lst.extend(re.sub("[^\w]", " ",  inputfile.readline()).split())
    queries.append(lst)
lst = None
chr = None
x = None
i = None

no_stmt = int(inputfile.readline())
KB = []   # 2D list for knowledge base
for i in range(no_stmt):
    lst1 = inputfile.readline().split(' | ')
    lst3 = []
    for list2 in lst1:
        lst = []
        if list2[0][0] == '~':
            lst.append('~')
        else:
            lst.append(' ')
        lst.extend(re.sub("[^\w]", " ",  list2).split())
        lst3.append(lst)
    KB.append(lst3)
lst1 = None
lst3 = None
lst = None
list2 = None
i = None

positive_index_table = []   # table for indexing the predicate format - [[predicate name, index to stmt #, ..],[],....]
negative_index_table = []   # table for indexing the predicate format - [[predicate name, index to stmt #, ..],[],....]
i = -1
for listoflist in KB:
    i = i+1
    for list in listoflist:
        if list[0] == '~':
            nlist = []
            if len(negative_index_table) == 0:
                nlist.append(list[1])
                nlist.append(i)
                negative_index_table.append(nlist)
            else:
                place = index_2d(negative_index_table, list[1])
                if place:
                    negative_index_table[place[0]].append(i)
                else:
                    nlist.append(list[1])
                    nlist.append(i)
                    negative_index_table.append(nlist)
        else:
            plist = []
            if len(positive_index_table) == 0:
                plist.append(list[1])
                plist.append(i)
                positive_index_table.append(plist)
            else:
                place = index_2d(positive_index_table, list[1])
                if place:
                    positive_index_table[place[0]].append(i)
                else:
                    plist.append(list[1])
                    plist.append(i)
                    positive_index_table.append(plist)

for query in queries:
    intermediate_result = []
    flag = 0
    value = False
    for list in KB:
        if list == [query]:
            outputfile.write('TRUE\n')
            flag = 1
            break
    if flag == 1:
        flag = 0
        continue
    insert_query = copy.deepcopy(query)
    if query[0] == '~':
        place = index_2d(negative_index_table, query[1])
        if place:
            for item in negative_index_table[place[0]][1:]:
                value = unify(KB[item], query)
                if value == True:
                    break
            if value == False:
                outputfile.write('FALSE\n')
            if value == True:
                outputfile.write('TRUE\n')
                continue
        else:
            outputfile.write('FALSE\n')
    else:
        place = index_2d(positive_index_table, query[1])
        if place:
            for item in positive_index_table[place[0]][1:]:
                value = unify(KB[item], query)
                if value == True:
                    break
            if value == False:
                outputfile.write('FALSE\n')
            if value == True:
                outputfile.write('TRUE\n')
                continue
        else:
            outputfile.write('FALSE\n')

inputfile.close()
outputfile.close()