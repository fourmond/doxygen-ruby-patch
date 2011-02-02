/******************************************************************************
 *
 * 
 *
 * Copyright (C) 1997-2011 by Dimitri van Heesch.
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
 * The translation into Portuguese was provided by
 *   Rui Godinho Lopes <rui@ruilopes.com>
 *     http://www.ruilopes.com
 *
 * VERSION HISTORY
 * ---------------
 * 007 09 june 2003
 *   ! Updated for doxygen v1.3.1
 * 006 30 july 2002
 *   ! Updated for doxygen v1.2.17
 * 005 10 july 2002
 *   ! Updated for doxygen v1.2.16
 * 004 03 march 2002
 *   ! Updated for doxygen v1.2.14
 * 003 23 november 2001
 *   - Removed some obsolete methods (latexBabelPackage, trAuthor, trAuthors and trFiles)
 * 002 19 november 2001
 *   ! Updated for doxygen v1.2.12
 * 001 20 july 2001
 *   ! Updated for doxygen v1.2.8.1
 * 000 ?
 *   + Initial translation for doxygen v1.1.5
 */

#ifndef TRANSLATOR_PT_H
#define TRANSLATOR_PT_H

class TranslatorPortuguese : public TranslatorAdapter_1_3_3
{
  public:

    // --- Language control methods -------------------

    /*! Used for identification of the language. The identification 
     * should not be translated. It should be replaced by the name 
     * of the language in English using lower-case characters only
     * (e.g. "czech", "japanese", "russian", etc.). It should be equal to 
     * the identification used in language.cpp.
     */
    QCString idLanguage()
    { return "portuguese"; }

    /*! Used to get the LaTeX command(s) for the language support. 
     *  This method should return string with commands that switch
     *  LaTeX to the desired language.  For example 
     *  <pre>"\\usepackage[german]{babel}\n"
     *  </pre>
     *  or
     *  <pre>"\\usepackage{polski}\n"
     *  "\\usepackage[latin2]{inputenc}\n"
     *  "\\usepackage[T1]{fontenc}\n"
     *  </pre>
     * 
     * The English LaTeX does not use such commands.  Because of this
     * the empty string is returned in this implementation.
     */
    virtual QCString latexLanguageSupportCommand()
    { return "Portuguese"; }

    /*! return the language charset. This will be used for the HTML output */
    virtual QCString idLanguageCharset()
    { return "iso-8859-1"; }

    // --- Language translation methods -------------------

    /*! used in the compound documentation before a list of related functions. */
    QCString trRelatedFunctions()
    { return "Fun��es associadas"; }

    /*! subscript for the related functions. */
    QCString trRelatedSubscript()
    { return "(Note que n�o s�o fun��es membro)"; }

    /*! header that is put before the detailed description of files, classes and namespaces. */
    QCString trDetailedDescription()
    { return "Descri��o detalhada"; }

    /*! header that is put before the list of typedefs. */
    QCString trMemberTypedefDocumentation()
    { return "Documenta��o das defini��es de tipo"; }

    /*! header that is put before the list of enumerations. */
    QCString trMemberEnumerationDocumentation()
    { return "Documenta��o das enumera��es"; }

    /*! header that is put before the list of member functions. */
    QCString trMemberFunctionDocumentation()
    { return "Documenta��o dos m�todos"; }

    /*! header that is put before the list of member attributes. */
    QCString trMemberDataDocumentation()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Documenta��o dos campos e atributos"; 
      }
      else
      {
        return "Documenta��o dos dados membro";
      }
    }

    /*! this is the text of a link put after brief descriptions. */
    QCString trMore()
    { return "Mais..."; }

    /*! put in the class documentation */
    QCString trListOfAllMembers()
    { return "Mostrar lista completa dos membros"; }

    /*! used as the title of the "list of all members" page of a class */
    QCString trMemberList()
    { return "Lista dos membros"; }

    /*! this is the first part of a sentence that is followed by a class name */
    QCString trThisIsTheListOfAllMembers()
    { return "Lista completa de todos os membros de "; }

    /*! this is the remainder of the sentence after the class name */
    QCString trIncludingInheritedMembers()
    { return ", incluindo todos os membros herdados."; }

    /*! this is put at the author sections at the bottom of man pages.
     *  parameter s is name of the project name.
     */
    QCString trGeneratedAutomatically(const char *s)
    { QCString result="Gerado automaticamente por Doxygen";
      if (s) result+=(QCString)" para "+s;
      result+=" a partir do c�digo fonte.";
      return result;
    }

    /*! put after an enum name in the list of all members */
    QCString trEnumName()
    { return "enumera��o"; }

    /*! put after an enum value in the list of all members */
    QCString trEnumValue()
    { return "valor enumerado"; }

    /*! put after an undocumented member in the list of all members */
    QCString trDefinedIn()
    { return "definido em"; }

    // quick reference sections

    /*! This is put above each page as a link to the list of all groups of
     *  compounds or files (see the \\group command).
     */
    QCString trModules()
    { return "M�dulos"; }

    /*! This is put above each page as a link to the class hierarchy */
    QCString trClassHierarchy()
    { return "Hierarquia de classes"; }

    /*! This is put above each page as a link to the list of annotated classes */
    QCString trCompoundList()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Estruturas de dados";
      }
      else
      {
        return "Lista de componentes";
      }
    }

    /*! This is put above each page as a link to the list of documented files */
    QCString trFileList()
    { return "Lista de ficheiros"; }

    /*! This is put above each page as a link to the list of all verbatim headers */
    QCString trHeaderFiles()
    { return "Ficheiros inclu�dos"; }

    /*! This is put above each page as a link to all members of compounds. */
    QCString trCompoundMembers()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Campos de dados";
      }
      else
      {
        return "Componentes membro";
      }
    }

    /*! This is put above each page as a link to all members of files. */
    QCString trFileMembers()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Globais";
      }
      else
      {
        return "Ficheiros membro";
      }
    }

    /*! This is put above each page as a link to all related pages. */
    QCString trRelatedPages()
    { return "P�ginas relacionadas"; }

    /*! This is put above each page as a link to all examples. */
    QCString trExamples()
    { return "Exemplos"; }

    /*! This is put above each page as a link to the search engine. */
    QCString trSearch()
    { return "Localizar"; }

    /*! This is an introduction to the class hierarchy. */
    QCString trClassHierarchyDescription()
    { return "Esta lista de heran�as est� organizada, dentro do poss�vel, por ordem alfab�tica:"; }

    /*! This is an introduction to the list with all files. */
    QCString trFileListDescription(bool extractAll)
    {
      QCString result="Lista de todos os ficheiros ";
      if (!extractAll) result+="documentados ";
      result+="com uma breve descri��o:";
      return result;
    }

    /*! This is an introduction to the annotated compound list. */
    QCString trCompoundListDescription()
    {       
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Lista das estruturas de dados com uma breve descri��o:";
      }
      else
      {
        return "Lista de classes, estruturas, uni�es e interfaces com uma breve descri��o:";
      }
    }

    /*! This is an introduction to the page with all class members. */
    QCString trCompoundMembersDescription(bool extractAll)
    {
      QCString result="Lista de todas as";
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        result+=" estruturas e campos de uni�es";
      }
      else
      {
        result+=" classes membro";
      }
      if (!extractAll)
      {
        result+=" documentadas";
      }
      result+=" com refer�ncia para ";
      if (!extractAll) 
      {
        if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
        {
          result+="a respectiva documenta��o:";
        }
        else
        {
          result+="a documenta��o de cada membro:";
        }
      }
      else 
      {
        if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
        {
          result+="as estruturas/uni�es a que pertencem:";
        }
        else
        {
          result+="as classes a que pertencem:";
        }
      }
      return result;
    }

    /*! This is an introduction to the page with all file members. */
    QCString trFileMembersDescription(bool extractAll)
    {
      QCString result="Lista de ";
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        result+="todas as fun��es, vari�veis, defini��es, enumera��es e defini��es de tipo ";
        if (!extractAll) result+="documentadas ";
      }
      else
      {
        result+="todos os ficheiros membro ";
        if (!extractAll) result+="documentados ";
      }
      result+="com refer�ncia para ";
      if (extractAll) 
        result+="o ficheiro a que pertecem:";
      else 
        result+="a respectiva documenta��o:";
      return result;
    }

    /*! This is an introduction to the page with the list of all header files. */
    QCString trHeaderFilesDescription()
    { return "Lista de todos os ficheiros cabe�alho que constituem a API:"; }

    /*! This is an introduction to the page with the list of all examples */
    QCString trExamplesDescription()
    { return "Lista de todos os exemplos:"; }

    /*! This is an introduction to the page with the list of related pages */
    QCString trRelatedPagesDescription()
    { return "Lista de documenta��o relacionada:"; }

    /*! This is an introduction to the page with the list of class/file groups */
    QCString trModulesDescription()
    { return "Lista de todos os m�dulos:"; }

    /*! This sentences is used in the annotated class/file lists if no brief
     * description is given.
     */
    QCString trNoDescriptionAvailable()
    { return "Nenhuma descri��o dispon�vel"; }

    // index titles (the project name is prepended for these)


    /*! This is used in HTML as the title of index.html. */
    QCString trDocumentation()
    { return "Documenta��o"; }

    /*! This is used in LaTeX as the title of the chapter with the
     * index of all groups.
     */
    QCString trModuleIndex()
    { return "�ndice dos m�dulos"; }

    /*! This is used in LaTeX as the title of the chapter with the
     * class hierarchy.
     */
    QCString trHierarchicalIndex()
    { return "�ndice da hierarquia"; }

    /*! This is used in LaTeX as the title of the chapter with the
     * annotated compound index.
     */
    QCString trCompoundIndex()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      { 
        return "�ndice das estruturas de dados";
      }
      else
      {
        return "�ndice dos componentes";
      }
    }

    /*! This is used in LaTeX as the title of the chapter with the
     * list of all files.
     */
    QCString trFileIndex()
    { return "�ndice dos ficheiros"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all groups.
     */
    QCString trModuleDocumentation()
    { return "Documenta��o do m�dulo"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all classes, structs and unions.
     */
    QCString trClassDocumentation()
    { return "Documenta��o da classe"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all files.
     */
    QCString trFileDocumentation()
    { return "Documenta��o do ficheiro"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all examples.
     */
    QCString trExampleDocumentation()
    { return "Documenta��o do exemplo"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all related pages.
     */
    QCString trPageDocumentation()
    { return "Documenta��o da p�gina"; }

    /*! This is used in LaTeX as the title of the document */
    QCString trReferenceManual()
    { return "Manual de refer�ncia"; }

    /*! This is used in the documentation of a file as a header before the
     *  list of defines
     */
    QCString trDefines()
    { return "Macros"; }

    /*! This is used in the documentation of a file as a header before the
     *  list of function prototypes
     */
    QCString trFuncProtos()
    { return "Prot�tipos de fun��es"; }

    /*! This is used in the documentation of a file as a header before the
     *  list of typedefs
     */
    QCString trTypedefs()
    { return "Defini��es de tipos"; }

    /*! This is used in the documentation of a file as a header before the
     *  list of enumerations
     */
    QCString trEnumerations()
    { return "Enumera��es"; }

    /*! This is used in the documentation of a file as a header before the
     *  list of (global) functions
     */
    QCString trFunctions()
    { return "Fun��es"; }

    /*! This is used in the documentation of a file as a header before the
     *  list of (global) variables
     */
    QCString trVariables()
    { return "Vari�veis"; }

    /*! This is used in the documentation of a file as a header before the
     *  list of (global) variables
     */
    QCString trEnumerationValues()
    { return "Valores da enumera��o"; }

    /*! This is used in the documentation of a file before the list of
     *  documentation blocks for defines
     */
    QCString trDefineDocumentation()
    { return "Documenta��o das macros"; }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for function prototypes
     */
    QCString trFunctionPrototypeDocumentation()
    { return "Documenta��o dos prot�tipos de fun��es"; }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for typedefs
     */
    QCString trTypedefDocumentation()
    { return "Documenta��o dos tipos"; }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for enumeration types
     */
    QCString trEnumerationTypeDocumentation()
    { return "Documenta��o dos valores da enumera��o"; }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for enumeration values
     */
    QCString trEnumerationValueDocumentation()
    { return "Documenta��o dos elementos da enumera��o"; }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for functions
     */
    QCString trFunctionDocumentation()
    { return "Documenta��o das fun��es"; }

    /*! This is used in the documentation of a file/namespace before the list
     *  of documentation blocks for variables
     */
    QCString trVariableDocumentation()
    { return "Documenta��o das vari�veis"; }

    /*! This is used in the documentation of a file/namespace/group before
     *  the list of links to documented compounds
     */
    QCString trCompounds()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Estruturas de Dados";
      }
      else
      {
        return "Componentes";
      }
    }

    /*! This is used in the standard footer of each page and indicates when
     *  the page was generated
     */
    QCString trGeneratedAt(const char *date,const char *projName)
    {
      QCString result=(QCString)"Gerado em "+date;
      if (projName) result+=(QCString)" para "+projName;
      result+=(QCString)" por";
      return result;
    }
    /*! This is part of the sentence used in the standard footer of each page.
     */
    QCString trWrittenBy()
    {
      return "escrito por";
    }

    /*! this text is put before a class diagram */
    QCString trClassDiagram(const char *clName)
    {
      return (QCString)"Diagrama de heran�as da classe "+clName;
    }

    /*! this text is generated when the \\internal command is used. */
    QCString trForInternalUseOnly()
    { return "Apenas para uso interno."; }

    /*! this text is generated when the \\reimp command is used. */
    QCString trReimplementedForInternalReasons()
    { return "Redefinido por raz�es internas; A interface n�o foi afectada.";
    }

    /*! this text is generated when the \\warning command is used. */
    QCString trWarning()
    { return "Aviso"; }

    /*! this text is generated when the \\bug command is used. */
    QCString trBugsAndLimitations()
    { return "Bugs e limita��es"; }

    /*! this text is generated when the \\version command is used. */
    QCString trVersion()
    { return "Vers�o"; }

    /*! this text is generated when the \\date command is used. */
    QCString trDate()
    { return "Data"; }

    /*! this text is generated when the \\return command is used. */
    QCString trReturns()
    { return "Retorna"; }

    /*! this text is generated when the \\sa command is used. */
    QCString trSeeAlso()
    { return "Veja tamb�m"; }

    /*! this text is generated when the \\param command is used. */
    QCString trParameters()
    { return "Par�metros"; }

    /*! this text is generated when the \\exception command is used. */
    QCString trExceptions()
    { return "Excep��es"; }

    /*! this text is used in the title page of a LaTeX document. */
    QCString trGeneratedBy()
    { return "Gerado por"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990307
//////////////////////////////////////////////////////////////////////////

    /*! used as the title of page containing all the index of all namespaces. */
    virtual QCString trNamespaceList()
    { return "Lista de namespaces"; }

    /*! used as an introduction to the namespace list */
    virtual QCString trNamespaceListDescription(bool extractAll)
    {
      QCString result="Lista ";
      if (!extractAll) result+="de toda a documenta��o ";
      result+="dos namespaces com uma breve descri��o:";
      return result;
    }

    /*! used in the class documentation as a header before the list of all
     *  friends of a class
     */
    virtual QCString trFriends()
    { return "Amigos"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990405
//////////////////////////////////////////////////////////////////////////

    /*! used in the class documentation as a header before the list of all
     * related classes
     */
    virtual QCString trRelatedFunctionDocumentation()
    { return "Documenta��o das classes amigas e fun��es relacionadas"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990425
//////////////////////////////////////////////////////////////////////////

    /*! used as the title of the HTML page of a class/struct/union */
    virtual QCString trCompoundReference(const char *clName,
                                    ClassDef::CompoundType compType,
                                    bool isTemplate)
    {
      QCString result="Refer�ncia ";
      switch(compType)
      {
        case ClassDef::Class:      result+="� classe "; break;
        case ClassDef::Struct:     result+="� estrutura "; break;
        case ClassDef::Union:      result+="� uni�o "; break;
        case ClassDef::Interface:  result+="ao interface "; break;
        case ClassDef::Protocol:   result+="protocol "; break; // translate me!
        case ClassDef::Category:   result+="category "; break; // translate me!
        case ClassDef::Exception:  result+="� excep��o "; break;
      }
      if (isTemplate) result+="Template ";
      result+=(QCString)clName;
      return result;
    }

    /*! used as the title of the HTML page of a file */
    virtual QCString trFileReference(const char *fileName)
    {
      QCString result= "Refer�ncia ao ficheiro ";
      result += fileName;
      return result;
    }

    /*! used as the title of the HTML page of a namespace */
    virtual QCString trNamespaceReference(const char *namespaceName)
    {
      QCString result= "Refer�ncia ao namespace ";
      result += namespaceName;
      return result;
    }

    /* these are for the member sections of a class, struct or union */
    virtual QCString trPublicMembers()
    { return "Membros p�blicos"; }
    virtual QCString trPublicSlots()
    { return "Slots p�blicos"; }
    virtual QCString trSignals()
    { return "Sinais"; }
    virtual QCString trStaticPublicMembers()
    { return "Membros p�blicos est�ticos"; }
    virtual QCString trProtectedMembers()
    { return "Membros protegidos"; }
    virtual QCString trProtectedSlots()
    { return "Slots protegidos"; }
    virtual QCString trStaticProtectedMembers()
    { return "Membros protegidos est�ticos"; }
    virtual QCString trPrivateMembers()
    { return "Membros privados"; }
    virtual QCString trPrivateSlots()
    { return "Slots privados"; }
    virtual QCString trStaticPrivateMembers()
    { return "Membros privados est�ticos"; }

    /*! this function is used to produce a comma-separated list of items.
     *  use generateMarker(i) to indicate where item i should be put.
     */
    virtual QCString trWriteList(int numEntries)
    {
      QCString result;
      int i;
      // the inherits list contain `numEntries' classes
      for (i=0;i<numEntries;i++)
      {
        // use generateMarker to generate placeholders for the class links!
        result+=generateMarker(i); // generate marker for entry i in the list
                                   // (order is left to right)

        if (i!=numEntries-1)  // not the last entry, so we need a separator
        {
          if (i<numEntries-2) // not the fore last entry
            result+=", ";
          else                // the fore last entry
            result+=" e ";
        }
      }
      return result;
    }

    /*! used in class documentation to produce a list of base classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritsList(int numEntries)
    {
      return "Derivada de "+trWriteList(numEntries)+".";
    }

    /*! used in class documentation to produce a list of super classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritedByList(int numEntries)
    {
      return "Herdado por "+trWriteList(numEntries)+".";
    }

    /*! used in member documentation blocks to produce a list of
     *  members that are hidden by this one.
     */
    virtual QCString trReimplementedFromList(int numEntries)
    {
      return "Reimplementado de "+trWriteList(numEntries)+".";
    }

    /*! used in member documentation blocks to produce a list of
     *  all member that overwrite the implementation of this member.
     */
    virtual QCString trReimplementedInList(int numEntries)
    {
      return "Reimplementado em "+trWriteList(numEntries)+".";
    }

    /*! This is put above each page as a link to all members of namespaces. */
    virtual QCString trNamespaceMembers()
    { return "Membros do namespace"; }

    /*! This is an introduction to the page with all namespace members */
    virtual QCString trNamespaceMemberDescription(bool extractAll)
    {
      QCString result="Lista ";
      if (extractAll) result+="de todos os ";
      else result+="de toda a documenta��o dos ";
      result+="membros do namespace com refer�ncia para ";
      if (extractAll)
        result+="a documenta��o de cada membro:";
      else
        result+="o namespace correspondente:";
      return result;
    }

  /*! This is used in LaTeX as the title of the chapter with the
     *  index of all namespaces.
     */
    virtual QCString trNamespaceIndex()
    { return "�ndice dos namespaces"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all namespaces.
     */
    virtual QCString trNamespaceDocumentation()
    { return "Documenta��o dos namespaces"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990522
//////////////////////////////////////////////////////////////////////////

    /*! This is used in the documentation before the list of all
     *  namespaces in a file.
     */
    virtual QCString trNamespaces()
    { return "Namespaces"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990728
//////////////////////////////////////////////////////////////////////////

    /*! This is put at the bottom of a class documentation page and is
     *  followed by a list of files that were used to generate the page.
     */
    virtual QCString trGeneratedFromFiles(ClassDef::CompoundType compType,
        bool single)
    { // here s is one of " Class", " Struct" or " Union"
      // single is true implies a single file
      QCString result=(QCString)"A documenta��o para ";
      switch(compType)
      {
        case ClassDef::Class:      result+="esta classe"; break;
        case ClassDef::Struct:     result+="esta estrutura"; break;
        case ClassDef::Union:      result+="esta uni�o"; break;
        case ClassDef::Interface:  result+="este interface"; break;
        case ClassDef::Protocol:   result+="protocol"; break; // translate me!
        case ClassDef::Category:   result+="category"; break; // translate me!
        case ClassDef::Exception:  result+="esta excep��o"; break;
      }
      result+=" foi gerada a partir ";
      if (single) result+=" do seguinte ficheiro:";
      else result+="dos seguintes ficheiros:";
      return result;
    }

    /*! This is in the (quick) index as a link to the alphabetical compound
     * list.
     */
    virtual QCString trAlphabeticalList()
    {
      return "Lista alfab�tica";
    }


//////////////////////////////////////////////////////////////////////////
// new since 0.49-990901
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the heading text for the retval command. */
    virtual QCString trReturnValues()
    { return "Valores retornados"; }

    /*! This is in the (quick) index as a link to the main page (index.html)
     */
    virtual QCString trMainPage()
    { return "P�gina principal"; }

    /*! This is used in references to page that are put in the LaTeX
     *  documentation. It should be an abbreviation of the word page.
     */
    virtual QCString trPageAbbreviation()
    { return "p. "; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991003
//////////////////////////////////////////////////////////////////////////

    virtual QCString trSources()
    {
      return "Fontes";
    }
    virtual QCString trDefinedAtLineInSourceFile()
    {
      return "Definido na linha @0 do ficheiro @1.";
    }
    virtual QCString trDefinedInSourceFile()
    {
      return "Definido no ficheiro @0.";
    }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991205
//////////////////////////////////////////////////////////////////////////

    virtual QCString trDeprecated()
    {
      return "Desaprovado";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.0.0
//////////////////////////////////////////////////////////////////////////

    /*! this text is put before a collaboration diagram */
    virtual QCString trCollaborationDiagram(const char *clName)
    {
      return (QCString)"Diagrama de colabora��o para "+clName+":";
    }
    /*! this text is put before an include dependency graph */
    virtual QCString trInclDepGraph(const char *fName)
    {
      return (QCString)"Diagrama de depend�ncias de inclus�o para "+fName+":";
    }
    /*! header that is put before the list of constructor/destructors. */
    virtual QCString trConstructorDocumentation()
    {
      return "Documenta��o dos Construtores & Destrutor";
    }
    /*! Used in the file documentation to point to the corresponding sources. */
    virtual QCString trGotoSourceCode()
    {
      return "Ir para o c�digo fonte deste ficheiro.";
    }
    /*! Used in the file sources to point to the corresponding documentation. */
    virtual QCString trGotoDocumentation()
    {
      return "Ir para a documenta��o deste ficheiro.";
    }
    /*! Text for the \\pre command */
    virtual QCString trPrecondition()
    {
      return "Precondi��o";
    }
    /*! Text for the \\post command */
    virtual QCString trPostcondition()
    {
      return "Poscondi��o";
    }
    /*! Text for the \\invariant command */
    virtual QCString trInvariant()
    {
      return "Invariante";
    }
    /*! Text shown before a multi-line variable/enum initialization */
    virtual QCString trInitialValue()
    {
      return "Valor inicial:";
    }
    /*! Text used the source code in the file index */
    virtual QCString trCode()
    {
      return "c�digo";
    }
    virtual QCString trGraphicalHierarchy()
    {
      return "Representa��o gr�fica da hiearquia da classe";
    }
    virtual QCString trGotoGraphicalHierarchy()
    {
      return "Ir para a representa��o gr�fica da hierarquia da classe";
    }
    virtual QCString trGotoTextualHierarchy()
    {
      return "Ir para a representa��o textual da hierarquia da classe";
    }
    virtual QCString trPageIndex()
    {
      return "�ndice da p�gina";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.0
//////////////////////////////////////////////////////////////////////////

    virtual QCString trNote()
    {
      return "Nota";
    }
    virtual QCString trPublicTypes()
    {
      return "Tipos P�blicos";
    }
    virtual QCString trPublicAttribs()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Campos de Dados";
      }
      else
      {
        return "Atributos P�blicos";
      }
    }
    virtual QCString trStaticPublicAttribs()
    {
      return "Atributos P�blicos Est�ticos";
    }
    virtual QCString trProtectedTypes()
    {
      return "Tipos Protegidos";
    }
    virtual QCString trProtectedAttribs()
    {
      return "Atributos Protegidos";
    }
    virtual QCString trStaticProtectedAttribs()
    {
      return "Atributos Protegidos Est�ticos";
    }
    virtual QCString trPrivateTypes()
    {
      return "Tipos Privados";
    }
    virtual QCString trPrivateAttribs()
    {
      return "Atributos Privados";
    }
    virtual QCString trStaticPrivateAttribs()
    {
      return "Atributos Privados Est�ticos";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a todo item */
    virtual QCString trTodo()
    {
      return "Tarefa";
    }
    /*! Used as the header of the todo list */
    virtual QCString trTodoList()
    {
      return "Lista de tarefas";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.4
//////////////////////////////////////////////////////////////////////////

    virtual QCString trReferencedBy()
    {
      return "Referenciado por";
    }
    virtual QCString trRemarks()
    {
      return "Observa��es";
    }
    virtual QCString trAttention()
    {
      return "Aten��o";
    }
    virtual QCString trInclByDepGraph()
    {
      return "Este grafo mostra quais s�o os ficheiros que incluem directamente ou indirectamente este ficheiro:";
    }
    virtual QCString trSince()
    {
      return "Desde";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.5
//////////////////////////////////////////////////////////////////////////

    /*! title of the graph legend page */
    virtual QCString trLegendTitle()
    {
      return "Legenda do grafo";
    }
    /*! page explaining how the dot graph's should be interpreted */
    virtual QCString trLegendDocs()
    {
      return
        "Esta p�gina explica como interpretar os grafos gerados pelo doxygen.<p>\n"
        "Considere o seguinte exemplo:\n"
        "\\code\n"
        "/*! Esta classe vai estar escondida devido � trunca��o */\n"
        "class Invisible { };\n\n"
        "/*! Esta classe tem a rela��o de heran�a escondida */\n"
        "class Truncated : public Invisible { };\n\n"
        "/* Classe n�o documentada por coment�rios doxygen */\n"
        "class Undocumented { };\n\n"
        "/*! Classe derivada usando deriva��o p�blica */\n"
        "class PublicBase : public Truncated { };\n\n"
        "/*! A template class */\n"
        "template<class T> class Templ { };\n\n"
        "/*! Classe derivada usando deriva��o protegida */\n"
        "class ProtectedBase { };\n\n"
        "/*! Classe derivada usando deriva��o privada */\n"
        "class PrivateBase { };\n\n"
        "/*! Classe usada pela classe Inherited */\n"
        "class Used { };\n\n"
        "/*! Super classe que deriva de v�rias classes */\n"
        "class Inherited : public PublicBase,\n"
        "                  protected ProtectedBase,\n"
        "                  private PrivateBase,\n"
        "                  public Undocumented,\n"
        "                  public Templ<int>\n"
        "{\n"
        "  private:\n"
        "    Used *m_usedClass;\n"
        "};\n"
        "\\endcode\n"
        "Se no ficheiro de configura��o estiver a tag \\c MAX_DOT_GRAPH_HEIGHT "
        "com o valor de 200 ent�o o seguinte grafo ser� gerado:"
        "<p><center><img src=\"graph_legend."+Config_getEnum("DOT_IMAGE_FORMAT")+"\"></center>\n"
        "<p>\n"
        "As caixas no grafo anterior t�m as seguintes interpreta��es:\n"
        "<ul>\n"
        "<li>Uma caixa inteiramente preta representa a estrutura ou a classe para "
        "a qual o grafo foi gerado.\n"
        "<li>Uma caixa com borda preta representa uma estrutura ou classe documentada.\n"
        "<li>Uma caixa com borda cinzenta representa uma estrutura ou classe n�o documentada.\n"
        "<li>Uma caixa com borda vermelha representa uma estrutura ou classe documentada onde "
        "nem todas as rela��es de heran�a/encapsulamento s�o exibidas. Um grafo � truncado "
        "quando n�o cabe na sua �rea predefinida.\n"
        "</ul>\n"
        "As setas t�m a seguinte interpreta��o:\n"
        "<ul>\n"
        "<li>Uma seta azul escura representa uma rela��o de heran�a p�blica entre duas classes.\n"
        "<li>Uma seta verde escura representa uma rela��o de heran�a protegida.\n"
        "<li>Uma seta vermelha escura representa uma rela��o de heran�a privada.\n"
        "<li>Uma seta rocha em tracejado representa uma rela��o de encapsulamento ou uso por "
        "parte de outra classe. A legenda da seta cont�m o nome da vari�vel ou vari�veis da "
        "rela��o. A seta aponta da classe que estabelece a rela��o para a classe ou estrutura que "
        "� acess�vel.\n"
        "</ul>\n";
    }
    /*! text for the link to the legend page */
    virtual QCString trLegend()
    {
      return "legenda";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.0
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a test item */
    virtual QCString trTest()
    {
      return "Teste";
    }
    /*! Used as the header of the test list */
    virtual QCString trTestList()
    {
      return "Lista de teste";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.1
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for KDE-2 IDL methods */
    virtual QCString trDCOPMethods()
    {
      return "M�todos DCOP";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.2
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for IDL properties */
    virtual QCString trProperties()
    {
      return "Propriedades";
    }
    /*! Used as a section header for IDL property documentation */
    virtual QCString trPropertyDocumentation()
    {
      return "Documenta��o das propriedades";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.4
//////////////////////////////////////////////////////////////////////////

    /*! Used for Java interfaces in the summary section of Java packages */
    virtual QCString trInterfaces()
    {
      return "Interfaces";
    }
    /*! Used for Java classes in the summary section of Java packages */
    virtual QCString trClasses()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Estruturas de dados";
      }
      else
      {
        return "Classes";
      }
    }
    /*! Used as the title of a Java package */
    virtual QCString trPackage(const char *name)
    {
      return (QCString)"Pacote "+name;
    }
    /*! Title of the package index page */
    virtual QCString trPackageList()
    {
      return "Lista de pacotes";
    }
    /*! The description of the package index page */
    virtual QCString trPackageListDescription()
    {
      return "Lista de pacotes com uma breve descri��o (se dispon�vel):";
    }
    /*! The link name in the Quick links header for each page */
    virtual QCString trPackages()
    {
      return "Pacotes";
    }
    /*! Used as a chapter title for Latex & RTF output */
    virtual QCString trPackageDocumentation()
    {
      return "Documenta��o do pacote";
    }
    /*! Text shown before a multi-line define */
    virtual QCString trDefineValue()
    {
      return "Valor:";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.5
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a \\bug item */
    virtual QCString trBug()
    {
      return "Bug";
    }
    /*! Used as the header of the bug list */
    virtual QCString trBugList()
    {
      return "Lista de Bugs";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.6
//////////////////////////////////////////////////////////////////////////

    /*! Used as ansicpg for RTF file
     *
     * The following table shows the correlation of Charset name, Charset Value and
     * <pre>
     * Codepage number:
     * Charset Name       Charset Value(hex)  Codepage number
     * ------------------------------------------------------
     * DEFAULT_CHARSET           1 (x01)
     * SYMBOL_CHARSET            2 (x02)
     * OEM_CHARSET             255 (xFF)
     * ANSI_CHARSET              0 (x00)            1252
     * RUSSIAN_CHARSET         204 (xCC)            1251
     * EE_CHARSET              238 (xEE)            1250
     * GREEK_CHARSET           161 (xA1)            1253
     * TURKISH_CHARSET         162 (xA2)            1254
     * BALTIC_CHARSET          186 (xBA)            1257
     * HEBREW_CHARSET          177 (xB1)            1255
     * ARABIC _CHARSET         178 (xB2)            1256
     * SHIFTJIS_CHARSET        128 (x80)             932
     * HANGEUL_CHARSET         129 (x81)             949
     * GB2313_CHARSET          134 (x86)             936
     * CHINESEBIG5_CHARSET     136 (x88)             950
     * </pre>
     *
     */
    virtual QCString trRTFansicp()
    {
      return "1252";
    }


    /*! Used as ansicpg for RTF fcharset
     *  \see trRTFansicp() for a table of possible values.
     */
    virtual QCString trRTFCharSet()
    {
      return "0";
    }

    /*! Used as header RTF general index */
    virtual QCString trRTFGeneralIndex()
    {
      return "�ndice";
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trClass(bool first_capital, bool singular)
    {
      QCString result((first_capital ? "Classe" : "classe"));
      if (!singular)  result+="s";
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trFile(bool first_capital, bool singular)
    {
      QCString result((first_capital ? "Ficheiro" : "ficheiro"));
      if (!singular)  result+="s";
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trNamespace(bool first_capital, bool singular)
    {
      QCString result((first_capital ? "Namespace" : "namespace"));
      if (!singular)  result+="s";
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trGroup(bool first_capital, bool singular)
    {
      QCString result((first_capital ? "Grupo" : "grupo"));
      if (!singular)  result+="s";
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trPage(bool first_capital, bool singular)
    {
      QCString result((first_capital ? "P�gina" : "p�gina"));
      if (!singular)  result+="s";
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trMember(bool first_capital, bool singular)
    {
      QCString result((first_capital ? "Membro" : "membro"));
      if (!singular)  result+="s";
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trField(bool first_capital, bool singular)
    {
      QCString result((first_capital ? "Campo" : "campo"));
      if (!singular)  result+="s";
      return result;
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names
     *  of the category.
     */
    virtual QCString trGlobal(bool first_capital, bool singular)
    {
      QCString result((first_capital ? "Globa" : "globa"));
      result+= singular? "l" : "ais";
      return result;
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.7
//////////////////////////////////////////////////////////////////////////

    /*! This text is generated when the \\author command is used and
     *  for the author section in man pages. */
    virtual QCString trAuthor(bool first_capital, bool singular)
    {
      QCString result((first_capital ? "Autor" : "autor"));
      if (!singular) result+="es";
      return result;
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.11
//////////////////////////////////////////////////////////////////////////

    /*! This text is put before the list of members referenced by a member
     */
    virtual QCString trReferences()
    {
      return "Refer�ncias";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.13
//////////////////////////////////////////////////////////////////////////

    /*! used in member documentation blocks to produce a list of 
     *  members that are implemented by this one.
     */
    virtual QCString trImplementedFromList(int numEntries)
    {
      return "Implementa "+trWriteList(numEntries)+".";
    }

    /*! used in member documentation blocks to produce a list of
     *  all members that implement this abstract member.
     */
    virtual QCString trImplementedInList(int numEntries)
    {
      return "Implementado em "+trWriteList(numEntries)+".";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.16
//////////////////////////////////////////////////////////////////////////

    /*! used in RTF documentation as a heading for the Table
     *  of Contents.
     */
    virtual QCString trRTFTableOfContents()
    {
      return "�ndice";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.17
//////////////////////////////////////////////////////////////////////////

    /*! Used as the header of the list of item that have been
     *  flagged deprecated
     */
    virtual QCString trDeprecatedList()
    {
      return "Lista de Deprecados";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.18
//////////////////////////////////////////////////////////////////////////

    /*! Used as a header for declaration section of the events found in 
     * a C# program
     */
    virtual QCString trEvents()
    {
      return "Eventos";
    }
    /*! Header used for the documentation section of a class' events. */
    virtual QCString trEventDocumentation()
    {
      return "Documenta��o dos eventos";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a heading for a list of Java class types with package scope.
     */
    virtual QCString trPackageTypes()
    { 
      return "Tipos do Pacote";
    }
    /*! Used as a heading for a list of Java class functions with package 
     * scope. 
     */
    virtual QCString trPackageMembers()
    { 
      return "Fun��es do Pacote";
    }
    /*! Used as a heading for a list of static Java class functions with 
     *  package scope.
     */
    virtual QCString trStaticPackageMembers()
    { 
      return "Fun��es Est�ticas do Pacote";
    }
    /*! Used as a heading for a list of Java class variables with package 
     * scope.
     */
    virtual QCString trPackageAttribs()
    { 
      return "Atributos do Pacote";
    }
    /*! Used as a heading for a list of static Java class variables with 
     * package scope.
     */
    virtual QCString trStaticPackageAttribs()
    { 
      return "Atributos Est�ticos do Pacote";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.3.1
//////////////////////////////////////////////////////////////////////////

    /*! Used in the quick index of a class/file/namespace member list page 
     *  to link to the unfiltered list of all members.
     */
    virtual QCString trAll()
    {
      return "Tudo";
    }
    /*! Put in front of the call graph for a function. */
    virtual QCString trCallGraph()
    {
      return "Grafo de chamadas desta fun��o:";
    }

};

#endif
