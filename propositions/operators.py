# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    if is_variable(formula.root):
        return formula

    if is_constant(formula.root):
        p = Formula('p')
        taut = Formula('|', p, Formula('~', p))  # (p|~p)
        return taut if formula.root == 'T' else Formula('~', taut)

    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))

    assert is_binary(formula.root)
    op = formula.root
    left = to_not_and_or(formula.first)
    right = to_not_and_or(formula.second)

    if op == '&':
        return Formula('&', left, right)
    if op == '|':
        return Formula('|', left, right)
    if op == '->':
        return Formula('|', Formula('~', left), right)
    if op == '+':
        return Formula('|',
                       Formula('&', left, Formula('~', right)),
                       Formula('&', Formula('~', left), right))
    if op == '<->':

        return Formula('|',
                       Formula('&', left, right),
                       Formula('&', Formula('~', left), Formula('~', right)))
    if op == '-&':
        return Formula('~', Formula('&', left, right))
    if op == '-|':
        return Formula('~', Formula('|', left, right))

    raise ValueError('Unknown operator: ' + op)
    # Task 3.5

def to_not_and(formula: Formula) -> Formula:
    f = to_not_and_or(formula)

    def rec(g: Formula) -> Formula:
        if is_variable(g.root):
            return g
        if is_constant(g.root):
            p = Formula('p')
            taut = Formula('|', p, Formula('~', p))
            g = taut if g.root == 'T' else Formula('~', taut)
            return rec(g)

        if is_unary(g.root):  # '~'
            return Formula('~', rec(g.first))

        assert is_binary(g.root)
        a = rec(g.first)
        b = rec(g.second)

        if g.root == '&':
            return Formula('&', a, b)
        if g.root == '|':
            return Formula('~', Formula('&', Formula('~', a), Formula('~', b)))

        raise ValueError('Unexpected operator in to_not_and: ' + g.root)

    return rec(f)
    # Task 3.6a

def to_nand(formula: Formula) -> Formula:
    f = to_not_and(formula)

    def nand(x: Formula, y: Formula) -> Formula:
        return Formula('-&', x, y)

    def rec(g: Formula) -> Formula:
        if is_variable(g.root):
            return g
        if is_constant(g.root):
            p = Formula('p')
            taut = nand(p, nand(p, p))
            return taut if g.root == 'T' else nand(taut, taut)

        if is_unary(g.root):
            a = rec(g.first)
            return nand(a, a)

        assert is_binary(g.root) and g.root == '&'
        a = rec(g.first)
        b = rec(g.second)
        t = nand(a, b)
        return nand(t, t)

    return rec(f)
    # Task 3.6b

def to_implies_not(formula: Formula) -> Formula:
    f = to_not_and_or(formula)

    def rec(g: Formula) -> Formula:
        if is_variable(g.root):
            return g
        if is_constant(g.root):
            p = Formula('p')
            t = Formula('->', p, p)
            return t if g.root == 'T' else Formula('~', t)

        if is_unary(g.root):
            return Formula('~', rec(g.first))

        assert is_binary(g.root)
        a = rec(g.first)
        b = rec(g.second)

        if g.root == '|':
            return Formula('->', Formula('~', a), b)
        if g.root == '&':
            return Formula('~', Formula('->', a, Formula('~', b)))

        raise ValueError('Unexpected operator in to_implies_not: ' + g.root)

    return rec(f)
    # Task 3.6c

def to_implies_false(formula: Formula) -> Formula:
    f = to_not_and_or(formula)

    F = Formula('F')

    def rec(g: Formula) -> Formula:
        if is_variable(g.root):
            return g
        if is_constant(g.root):
            return F if g.root == 'F' else Formula('->', F, F)

        if is_unary(g.root):
            a = rec(g.first)
            return Formula('->', a, F)

        assert is_binary(g.root)
        a = rec(g.first)
        b = rec(g.second)

        if g.root == '|':
            return Formula('->', Formula('->', a, F), b)
        if g.root == '&':
            return Formula('->', Formula('->', a, Formula('->', b, F)), F)

        raise ValueError('Unexpected operator in to_implies_false: ' + g.root)

    return rec(f)
    # Task 3.6d
