#lang racket

(provide tokenize)

;; The `[data #f]` is a default value for the 2nd positional argument.
;; That way, this function can take 1 arg or 2 args.
(define (token type [data #f])
  (list type data))

;;;; Token creator functions
;;;;
;;;; Given a string matching a regexp, return a token for that input or #f for
;;;; no token.

(define (skip-match str) #f)

(define (punctuation-token str)
  (token
    (case str
      [("(") 'OPAREN]
      [(")") 'CPAREN])))

(define (number-token type)
  ;; Note the indirection here: the first call returns a function of 1 argument.
  (λ (str) (token type (string->number str))))

(define (string-token str)
  (let* ([len (string-length str)]
         [inner-string (substring str 1 (sub1 len))] ; strip first & last quotes
         [unescaped-char (λ (_ char) (if (equal? "n" char) "\n" char))]
         [unescaped-str (regexp-replace #rx"\\\\(.)"
                                        inner-string unescaped-char)])
    (token 'STRING unescaped-str)))

(define (define-or-name-token str)
  (if (equal? "define" str)
      (token 'DEFINE)
      (if (equal? "let" str)
          (token 'LET)
          (if (equal? "lambda" str)
              (token 'LAMBDA)
              (token 'NAME (string->symbol str))))))

;;;; Tokenizing rules table
;;;;
;;;; Each item in the table is a 2-tuple (i.e. list of 2 elements):
;;;; 1. a regexp to detect a token at the beginning of a string
;;;; 2. a function (from above) to take the matched string and create a token

(define re-table
  (list
    (list #rx"^[ \r\n\t]+" skip-match) ; whitespace
    (list #rx"^;\\*.*?\\*;" skip-match) ; /* */ comments
    (list #rx"^;;[^\n]+(\n|$)" skip-match) ; // comments
    (list #rx"^[()]" punctuation-token)
    (list #rx"^-?[0-9]+\\.[0-9]+(?=[\r\n\t (){},;.]|$)" (number-token 'FLOAT))
    (list #rx"^-?[0-9]+(?=[\r\n\t (){},;.]|$)" (number-token 'INT))
    (list #rx"^\"[^\"\\\\]*(\\\\.[^\"\\\\]*)*\"(?=[\r\n\t (){},;.]|$)"
          string-token)
    (list #rx"^[^(){},;.\" \r\n\t0-9][^(){},;.\" \r\n\t]*(?=[\r\n\t (){},;.]|$)"
          define-or-name-token)))

;;;; Tokenizing engine

;; Given the current input string and a tokenizing rule tuple, try to match. If no
;; match, return #f. If match, return the match and the corresponding token.
(define (table-entry->result input entry)
  (let* ([regexp (first entry)]
         [process-match (second entry)]
         [matches (regexp-match regexp input)])
    (if (not matches)
      #f
      (let* ([match (first matches)]
             [token (process-match match)])
        (list (string-length match) match token)))))

;; Break the input string up into a list of tokens.
;; This function is recursive, returning a pair of the front token and the
;; result of a recursive call on the remaining input.
(define (tokenize input)
  (if (zero? (string-length input))
    null
    ;; filter-map calls map (which calls the function once per item) and
    ;; removes #f results.
    (let ([match-results (filter-map (λ (entry) (table-entry->result input entry))
                                     re-table)])
      (if (empty? match-results)
        (list (token 'INVALID input))
        (let* ([longest-match-result (first (sort match-results > #:key first))]
               [longest-match-length (first longest-match-result)]
               [longest-match (second longest-match-result)]
               [token (third longest-match-result)]
               [remaining-input (substring input longest-match-length)])
          (if token
            (cons token (tokenize remaining-input))
            (tokenize remaining-input)))))))

(module+ test
  (require (only-in rackunit
                    check-equal?))

  (check-equal? (tokenize "define") (list (token 'DEFINE #f)))
  (check-equal? (tokenize "") null)
  (check-equal? (tokenize " \n\t\r ") null)
  (check-equal? (tokenize ";; comment1") null)
  (check-equal? (tokenize ";; comment1\n7") (list (token 'INT 7)))
  (check-equal? (tokenize ";* comment2 \n *;\n8") (list (token 'INT 8)))
  (check-equal? (tokenize "\"\"") (list (token 'STRING "")))
  (check-equal? (tokenize "\"abc\"") (list (token 'STRING "abc")))
  (check-equal? (tokenize "if1") (list (token 'NAME 'if1)))
  (check-equal? (tokenize "1if") (list (token 'INVALID "1if")))
  (check-equal? (tokenize "9.8") (list (token 'FLOAT 9.8)))
  (check-equal? (tokenize "9") (list (token 'INT 9)))
  (check-equal? (tokenize "1a") (list (token 'INVALID "1a")))
  (check-equal? (tokenize "123\"456\"") (list (token 'INVALID "123\"456\"")))
  (check-equal? (tokenize "\"123\"456") (list (token 'INVALID "\"123\"456")))
  (check-equal? (tokenize "abc\"def\"") (list (token 'INVALID "abc\"def\"")))
  (check-equal? (tokenize "\"abc\"def") (list (token 'INVALID "\"abc\"def")))
  (check-equal? (tokenize "\"\\\\\"\"") (list (token 'INVALID "\"\\\\\"\"")))
  (check-equal? (tokenize "\"a\\\\nbc\"") (list (token 'STRING "a\\nbc")))
  (check-equal? (tokenize "\"\\\"\"") (list (token 'STRING "\"")))
  (check-equal? (tokenize "\"\\n\"") (list (token 'STRING "\n")))
  (check-equal? (tokenize "\"\\\\\"") (list (token 'STRING "\\")))

  (define example-program "
define factorial = fun (n)
  ;; first check base case
  if(<(n 0.9)
     1
     factorial(-(n 1)) ;* recursive case *; )

print(+(\"5! is \" factorial(5)))")

  (define example-program-tokens
    (list
      (list 'DEFINE    #f)
      (list 'NAME      'factorial)
      (list 'NAME      '=)
      (list 'NAME      'fun)
      (list 'OPAREN    #f)
      (list 'NAME      'n)
      (list 'CPAREN    #f)
      (list 'NAME      'if)
      (list 'OPAREN    #f)
      (list 'NAME      '<)
      (list 'OPAREN    #f)
      (list 'NAME      'n)
      (list 'FLOAT     0.9)
      (list 'CPAREN    #f)
      (list 'INT       1)
      (list 'NAME      'factorial)
      (list 'OPAREN    #f)
      (list 'NAME      '-)
      (list 'OPAREN    #f)
      (list 'NAME      'n)
      (list 'INT       1)
      (list 'CPAREN    #f)
      (list 'CPAREN    #f)
      (list 'CPAREN    #f)
      (list 'NAME      'print)
      (list 'OPAREN    #f)
      (list 'NAME      '+)
      (list 'OPAREN    #f)
      (list 'STRING    "5! is ")
      (list 'NAME      'factorial)
      (list 'OPAREN    #f)
      (list 'INT       5)
      (list 'CPAREN    #f)
      (list 'CPAREN    #f)
      (list 'CPAREN    #f)))

  (check-equal? (tokenize example-program) example-program-tokens))