/******************************************************************************
 *
 * 
 *
 * Copyright (C) 1997-2008 by Dimitri van Heesch.
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation under the terms of the GNU General Public License is hereby 
 * granted. No representations are made about the suitability of this software 
 * for any purpose. It is provided "as is" without express or implied warranty.
 * See the GNU General Public License for more details.
 *
 * Documents produced by Doxygen are derivative works derived from the
 * input used in their production; they are not affected by this license.
 *
 */
/*  This code is based on the work done by the MoxyPyDoxy team
 *  (Linda Leong, Mike Rivera, Kim Truong, and Gabriel Estrada)
 *  in Spring 2005 as part of CS 179E: Compiler Design Project
 *  at the University of California, Riverside; the course was
 *  taught by Peter H. Froehlich <phf@acm.org>.
 */


#ifndef RUBYSCANNER_H
#define RUBYSCANNER_H

#include "parserintf.h"

/** \brief Ruby Language parser using state-based lexical scanning.
 *
 * This is the Ruby language parser for doxygen.
 */
class RubyLanguageScanner : public ParserInterface
{
public:
  virtual ~RubyLanguageScanner() {}
  void parseInput(const char * fileName, 
		  const char *fileBuf, 
		  Entry *root);
  bool needsPreprocessing(const QCString &extension);
  void parseCode(CodeOutputInterface &codeOutIntf,
		 const char *scopeName,
		 const QCString &input,
		 bool isExampleBlock,
		 const char *exampleName=0,
		 FileDef *fileDef=0,
		 int startLine=-1,
		 int endLine=-1,
		 bool inlineFragment=FALSE,
		 MemberDef *memberDef=0
		 );
  void resetCodeParserState();
  void parsePrototype(const char *text);
  
  /// This is a small class for internal use whose job is to keep
  /// information about the context in which the scanner is.
  class ScannerContext {
  public:
    /// Is is OK to end an expression on a newline ?
    bool newLineOK;
    
    /// Is there a pending unescaped backspace ?
    bool pendingBackspace;

    /// Is it OK to begin a class/function definition ?
    bool definitionOK;

    /// Is the next thing surely an expression ?
    bool surelyExpression;

    /// True if the next thing cannot be a definition -- but could be
    /// an expression.
    bool noDefinition;

    /// Can an expression be started ? 
    bool expressionOK;

    /// Whether if/until and so on start a new block ?
    bool ifNewBlock; 

    /// Whether or not we can finish the current expression
    bool canEndExpression;

    /// Reset the state to a Beginning-of-file one
    void reset();

    ScannerContext() { reset();};

    
    /// Parses one character and updates the state of the context.
    void parseOneChar(char ch);
  };
};

void rubyscanFreeScanner();

#endif
