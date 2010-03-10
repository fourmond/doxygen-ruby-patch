/******************************************************************************
 *
 * 
 *
 * Copyright (C) 1997-2010 by Dimitri van Heesch.
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
 
 /*
  * Original Hungarian translation by
  * Gy�rgy F�ldv�ri  <foldvari@diatronltd.com>
  *
  * Extended, revised and updated by
  * �kos Kiss  <akiss@users.sourceforge.net>
  *
  * Further extended, revised and updated by
  * Tam�si Ferenc <tf551@hszk.bme.hu>
  */

#ifndef TRANSLATOR_HU_H
#define TRANSLATOR_HU_H

class TranslatorHungarian : public TranslatorAdapter_1_4_6
{
  private:
    const char * zed(char c)
    {
        switch (c & ~('a' ^ 'A')) {
            case 'B': case 'C': case 'D': case 'F': case 'G':
            case 'H': case 'J': case 'K': case 'L': case 'M':
            case 'N': case 'P': case 'Q': case 'R': case 'S':
            case 'T': case 'V': case 'W': case 'X': case 'Z':
                return "  ";
            default:
                return "z ";
        }
    }
  public:

    // --- Language control methods -------------------
    virtual QCString idLanguage()
    { return "hungarian"; }
    /*! Used to get the command(s) for the language support. This method
     *  was designed for languages which do not prefer babel package.
     *  If this methods returns empty string, then the latexBabelPackage()
     *  method is used to generate the command for using the babel package.
     */
    virtual QCString latexLanguageSupportCommand()
    {
      return "\\usepackage[T2A]{fontenc}\n"
             "\\usepackage[magyar]{babel}\n";
    }

    /*! return the language charset. This will be used for the HTML output */
    virtual QCString idLanguageCharset()
    {
      return "iso-8859-2";
    }

    // --- Language translation methods -------------------

    /*! used in the compound documentation before a list of related functions. */
    virtual QCString trRelatedFunctions()
    { return "Kapcsol�d� f�ggv�nyek"; }

    /*! subscript for the related functions. */
    virtual QCString trRelatedSubscript()
    { return "(Figyelem! Ezek a f�ggv�nyek nem tagjai az oszt�lynak!)"; }

    /*! header that is put before the detailed description of files, classes and namespaces. */
    virtual QCString trDetailedDescription()
    { return "R�szletes le�r�s"; }

    /*! header that is put before the list of typedefs. */
    virtual QCString trMemberTypedefDocumentation()
    { return "T�pusdefin�ci�-tagok dokument�ci�ja"; }
    
    /*! header that is put before the list of enumerations. */
    virtual QCString trMemberEnumerationDocumentation()
    { return "Enumer�ci�-tagok dokument�ci�ja"; }
    
    /*! header that is put before the list of member functions. */
    virtual QCString trMemberFunctionDocumentation()
    { return "Tagf�ggv�nyek dokument�ci�ja"; }
    
    /*! header that is put before the list of member attributes. */
    virtual QCString trMemberDataDocumentation()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Adatmez�k dokument�ci�ja"; 
      }
      else
      {
        return "Adattagok dokument�ci�ja"; 
      }
    }

    /*! this is the text of a link put after brief descriptions. */
    virtual QCString trMore()
    { return "R�szletek..."; }

    /*! put in the class documentation */
    virtual QCString trListOfAllMembers()
    { return "A tagok teljes list�ja."; }

    /*! used as the title of the "list of all members" page of a class */
    virtual QCString trMemberList()
    { return "Taglista"; }

    /*! this is the first part of a sentence that is followed by a class name */
    virtual QCString trThisIsTheListOfAllMembers()
    { return "A(z) "; }

    /*! this is the remainder of the sentence after the class name */
    virtual QCString trIncludingInheritedMembers()
    { return " oszt�ly tagjainak teljes list�ja, az �r�k�lt tagokkal egy�tt."; }
    
    virtual QCString trGeneratedAutomatically(const char *s)
    { QCString result="Ezt a dokument�ci�t a Doxygen k�sz�tette ";
      if (s) result+=(QCString)" a" + zed(s[0])+s+(QCString)" projekthez";
      result+=" a forr�sk�db�l."; 
      return result;
    }

    /*! put after an enum name in the list of all members */
    virtual QCString trEnumName()
    { return "enum"; }
    
    /*! put after an enum value in the list of all members */
    virtual QCString trEnumValue()
    { return "enum-�rt�k"; }
    
    /*! put after an undocumented member in the list of all members */
    virtual QCString trDefinedIn()
    { return "defini�lja:"; }

    // quick reference sections

    /*! This is put above each page as a link to the list of all groups of 
     *  compounds or files (see the \\group command).
     */
    virtual QCString trModules()
    { return "Modulok"; }
    
    /*! This is put above each page as a link to the class hierarchy */
    virtual QCString trClassHierarchy()
    { return "Oszt�lyhierarchia"; }
    
    /*! This is put above each page as a link to the list of annotated classes */
    virtual QCString trCompoundList()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Adatszerkezetek";
      }
      else
      {
        return "Oszt�lylista"; 
      }
    }
    
    /*! This is put above each page as a link to the list of documented files */
    virtual QCString trFileList()
    { return "F�jllista"; }

    /*! This is put above each page as a link to all members of compounds. */
    virtual QCString trCompoundMembers()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Adatmez�k"; 
      }
      else
      {
        return "Oszt�lytagok"; 
      }
    }

    /*! This is put above each page as a link to all members of files. */
    virtual QCString trFileMembers()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Glob�lis elemek"; 
      }
      else
      {
        return "F�jlelemek"; 
      }
    }

    /*! This is put above each page as a link to all related pages. */
    virtual QCString trRelatedPages()
    { return "Kapcsol�d� lapok"; }

    /*! This is put above each page as a link to all examples. */
    virtual QCString trExamples()
    { return "P�ld�k"; }

    /*! This is put above each page as a link to the search engine. */
    virtual QCString trSearch()
    { return "Keres�s"; }

    /*! This is an introduction to the class hierarchy. */
    virtual QCString trClassHierarchyDescription()
    { return "Majdnem (de nem teljesen) bet�rendbe szedett "
             "lesz�rmaz�si lista:";
    }

    /*! This is an introduction to the list with all files. */
    virtual QCString trFileListDescription(bool extractAll)
    {
      QCString result="Az �sszes ";
      if (!extractAll) result+="dokument�lt ";
      result+="f�jl list�ja r�vid le�r�sokkal:";
      return result;
    }

    /*! This is an introduction to the annotated compound list. */
    virtual QCString trCompoundListDescription()
    { 
      
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Az �sszes adatszerkezet list�ja r�vid le�r�sokkal:"; 
      }
      else
      {
        return "Az �sszes oszt�ly, strukt�ra, uni� �s interf�sz "
               "list�ja r�vid le�r�sokkal:"; 
      }
    }

    /*! This is an introduction to the page with all class members. */
    virtual QCString trCompoundMembersDescription(bool extractAll)
    {
      QCString result="Az �sszes ";
      if (!extractAll)
      {
        result+="dokument�lt ";
      }
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        result+="strukt�ra- �s �ni�mez�";
      }
      else
      {
        result+="oszt�lytag";
      }
      result+=" list�ja, valamint hivatkoz�s ";
      if (!extractAll) 
      {
        if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
        {
          result+="a megfelel� strukt�ra-/�ni�dokument�ci�ra minden mez�n�l:";
        }
        else
        {
          result+="a megfelel� oszt�lydokument�ci�ra minden tagn�l:";
        }
      }
      else 
      {
        if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
        {
          result+="a strukt�r�kra/�ni�kra, amikhez tartoznak:";
        }
        else
        {
          result+="az oszt�lyokra, amikhez tartoznak:";
        }
      }
      return result;
    }

    /*! This is an introduction to the page with all file members. */
    virtual QCString trFileMembersDescription(bool extractAll)
    {
      QCString result="Az �sszes ";
      if (!extractAll) result+="dokument�lt ";
      
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        result+="f�ggv�ny, v�ltoz�, makr�defin�ci�, enumer�ci� �s t�pusdefin�ci�";
      }
      else
      {
        result+="f�jlelem";
      }
      result+=" list�ja, valamint hivatkoz�s ";
      if (extractAll) 
        result+="a f�jlokra, amikhez tartoznak:";
      else 
        result+="a dokument�ci�ra:";
      return result;
    }

    /*! This is an introduction to the page with the list of all examples */
    virtual QCString trExamplesDescription()
    { return "A p�ld�k list�ja:"; }

    /*! This is an introduction to the page with the list of related pages */
    virtual QCString trRelatedPagesDescription()
    { return "A kapcsol�d� dokument�ci�k list�ja:"; }

    /*! This is an introduction to the page with the list of class/file groups */
    virtual QCString trModulesDescription()
    { return "A modulok list�ja:"; }

    // index titles (the project name is prepended for these) 


    /*! This is used in HTML as the title of index.html. */
    virtual QCString trDocumentation()
    { return "Dokument�ci�"; }

    /*! This is used in LaTeX as the title of the chapter with the 
     * index of all groups.
     */
    virtual QCString trModuleIndex()
    { return "Modulmutat�"; }

    /*! This is used in LaTeX as the title of the chapter with the 
     * class hierarchy.
     */
    virtual QCString trHierarchicalIndex()
    { return "Hierarchikus mutat�"; }

    /*! This is used in LaTeX as the title of the chapter with the 
     * annotated compound index.
     */
    virtual QCString trCompoundIndex()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      { 
        return "Adatszerkezet-mutat�";
      }
      else
      {
        return "Oszt�lymutat�"; 
      }
    }

    /*! This is used in LaTeX as the title of the chapter with the
     * list of all files.
     */
    virtual QCString trFileIndex()
    { return "F�jlmutat�"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all groups.
     */
    virtual QCString trModuleDocumentation()
    { return "Modulok dokument�ci�ja"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all classes, structs and unions.
     */
    virtual QCString trClassDocumentation()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Adatszerkezetek dokument�ci�ja";
      }
      else
      {
        return "Oszt�lyok dokument�ci�ja";
      }
    }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all files.
     */
    virtual QCString trFileDocumentation()
    { return "F�jlok dokument�ci�ja"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all examples.
     */
    virtual QCString trExampleDocumentation()
    { return "P�ld�k dokument�ci�ja"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all related pages.
     */
    virtual QCString trPageDocumentation()
    { return "Kapcsol�d� dokument�ci�k"; }

    /*! This is used in LaTeX as the title of the document */
    virtual QCString trReferenceManual()
    { return "Referencia k�zik�nyv"; }
    
    /*! This is used in the documentation of a file as a header before the 
     *  list of defines
     */
    virtual QCString trDefines()
    { return "Makr�defin�ci�k"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of function prototypes
     */
    virtual QCString trFuncProtos()
    { return "F�ggv�ny-protot�pusok"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of typedefs
     */
    virtual QCString trTypedefs()
    { return "T�pusdefin�ci�k"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of enumerations
     */
    virtual QCString trEnumerations()
    { return "Enumer�ci�k"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) functions
     */
    virtual QCString trFunctions()
    { return "F�ggv�nyek"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) variables
     */
    virtual QCString trVariables()
    { return "V�ltoz�k"; }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) variables
     */
    virtual QCString trEnumerationValues()
    { return "Enumer�ci�-�rt�kek"; }
    
    /*! This is used in the documentation of a file before the list of
     *  documentation blocks for defines
     */
    virtual QCString trDefineDocumentation()
    { return "Makr�defin�ci�k dokument�ci�ja"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for function prototypes
     */
    virtual QCString trFunctionPrototypeDocumentation()
    { return "F�ggv�ny-protot�pusok dokument�ci�ja"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for typedefs
     */
    virtual QCString trTypedefDocumentation()
    { return "T�pusdefin�ci�k dokument�ci�ja"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for enumeration types
     */
    virtual QCString trEnumerationTypeDocumentation()
    { return "Enumer�ci�k dokument�ci�ja"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for functions
     */
    virtual QCString trFunctionDocumentation()
    { return "F�ggv�nyek dokument�ci�ja"; }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for variables
     */
    virtual QCString trVariableDocumentation()
    { return "V�ltoz�k dokument�ci�ja"; }

    /*! This is used in the documentation of a file/namespace/group before 
     *  the list of links to documented compounds
     */
    virtual QCString trCompounds()
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Adatszerkezetek"; 
      }
      else
      {
        return "Oszt�lyok"; 
      }
    }

    /*! This is used in the standard footer of each page and indicates when 
     *  the page was generated 
     */
    virtual QCString trGeneratedAt(const char *date,const char *projName)
    { 
      QCString result=(QCString)"";
      if (projName) result+=(QCString)"Projekt: "+projName;
      result+=(QCString)" K�sz�lt: "+date+" K�sz�tette: ";
      return result;
    }
    /*! This is part of the sentence used in the standard footer of each page.
     */
    virtual QCString trWrittenBy()
    {
      return " melyet �rt ";
    }

    /*! this text is put before a class diagram */
    virtual QCString trClassDiagram(const char *clName)
    {
      return (QCString)"A"+zed(clName[0])+clName+" oszt�ly sz�rmaz�si diagramja:";
    }
    
    /*! this text is generated when the \\internal command is used. */
    virtual QCString trForInternalUseOnly()
    { return "CSAK BELS� HASZN�LATRA!"; }

    /*! this text is generated when the \\warning command is used. */
    virtual QCString trWarning()
    { return "Figyelmeztet�s"; }

    /*! this text is generated when the \\version command is used. */
    virtual QCString trVersion()
    { return "Verzi�"; }

    /*! this text is generated when the \\date command is used. */
    virtual QCString trDate()
    { return "D�tum"; }

    /*! this text is generated when the \\return command is used. */
    virtual QCString trReturns()
    { return "Visszat�r�si �rt�k"; }

    /*! this text is generated when the \\sa command is used. */
    virtual QCString trSeeAlso()
    { return "L�sd m�g"; }

    /*! this text is generated when the \\param command is used. */
    virtual QCString trParameters()
    { return "Param�terek"; }

    /*! this text is generated when the \\exception command is used. */
    virtual QCString trExceptions()
    { return "Kiv�telek"; }
    
    /*! this text is used in the title page of a LaTeX document. */
    virtual QCString trGeneratedBy()
    { return "K�sz�tette"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990307
//////////////////////////////////////////////////////////////////////////
    
    /*! used as the title of page containing all the index of all namespaces. */
    virtual QCString trNamespaceList()
    { return "N�vt�rlista"; }

    /*! used as an introduction to the namespace list */
    virtual QCString trNamespaceListDescription(bool extractAll)
    {
      QCString result="Az �sszes ";
      if (!extractAll) result+="dokument�lt ";
      result+="n�vt�r list�ja r�vid le�r�sokkal:";
      return result;
    }

    /*! used in the class documentation as a header before the list of all
     *  friends of a class
     */
    virtual QCString trFriends()
    { return "Bar�tok"; }
    
//////////////////////////////////////////////////////////////////////////
// new since 0.49-990405
//////////////////////////////////////////////////////////////////////////
    
    /*! used in the class documentation as a header before the list of all
     * related classes 
     */
    virtual QCString trRelatedFunctionDocumentation()
    { return "Bar�t �s kapcsol�d� f�ggv�nyek dokument�ci�ja"; }
    
//////////////////////////////////////////////////////////////////////////
// new since 0.49-990425
//////////////////////////////////////////////////////////////////////////

    /*! used as the title of the HTML page of a class/struct/union */
    virtual QCString trCompoundReference(const char *clName,
                                    ClassDef::CompoundType compType,
                                    bool isTemplate)
    {
      QCString result=(QCString)clName;
      switch(compType)
      {
        case ClassDef::Class:      result+=" oszt�ly"; break;
        case ClassDef::Struct:     result+=" strukt�ra"; break;
        case ClassDef::Union:      result+=" uni�"; break;
        case ClassDef::Interface:  result+=" interf�sz"; break;
        case ClassDef::Protocol:   result+=" protocol"; break; // translate me!
        case ClassDef::Category:   result+=" category"; break; // translate me!
        case ClassDef::Exception:  result+=" kiv�tel"; break;
      }
      if (isTemplate) result+="sablon-";
      result+="referencia";
      return result;
    }

    /*! used as the title of the HTML page of a file */
    virtual QCString trFileReference(const char *fileName)
    {
      QCString result=fileName;
      result+=" f�jlreferencia"; 
      return result;
    }

    /*! used as the title of the HTML page of a namespace */
    virtual QCString trNamespaceReference(const char *namespaceName)
    {
      QCString result=namespaceName;
      result+=" n�vt�r-referencia";
      return result;
    }
    
    virtual QCString trPublicMembers()
    { return "Publikus tagf�ggv�nyek"; }
    virtual QCString trPublicSlots()
    { return "Publikus r�sek"; }
    virtual QCString trSignals()
    { return "Szign�lok"; }
    virtual QCString trStaticPublicMembers()
    { return "Statikus publikus tagf�ggv�nyek"; }
    virtual QCString trProtectedMembers()
    { return "V�dett tagf�ggv�nyek"; }
    virtual QCString trProtectedSlots()
    { return "V�dett r�sek"; }
    virtual QCString trStaticProtectedMembers()
    { return "Statikus v�dett tagf�ggv�nyek"; }
    virtual QCString trPrivateMembers()
    { return "Priv�t tagf�ggv�nyek"; }
    virtual QCString trPrivateSlots()
    { return "Priv�t r�sek"; }
    virtual QCString trStaticPrivateMembers()
    { return "Statikus priv�t tagf�ggv�nyek"; }
    
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
            result+=" �s ";
        }
      }
      return result; 
    }
    
    /*! used in class documentation to produce a list of base classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritsList(int numEntries)
    {
      return "�s�k: "+trWriteList(numEntries)+".";
    }

    /*! used in class documentation to produce a list of super classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritedByList(int numEntries)
    {
      return "Lesz�rmazottak: "+trWriteList(numEntries)+".";
    }

    /*! used in member documentation blocks to produce a list of 
     *  members that are hidden by this one.
     */
    virtual QCString trReimplementedFromList(int numEntries)
    {
      return "�jraimplement�lt �s�k: "+trWriteList(numEntries)+".";
    }

    /*! used in member documentation blocks to produce a list of
     *  all member that overwrite the implementation of this member.
     */
    virtual QCString trReimplementedInList(int numEntries)
    {
      return "�jraimplement�l� lesz�rmazottak: "+trWriteList(numEntries)+".";
    }

    /*! This is put above each page as a link to all members of namespaces. */
    virtual QCString trNamespaceMembers()
    { return "N�vt�rtagok"; }

    /*! This is an introduction to the page with all namespace members */
    virtual QCString trNamespaceMemberDescription(bool extractAll)
    { 
      QCString result="Az �sszes ";
      if (!extractAll) result+="dokument�lt ";
      result+="n�vt�r tagjainak list�ja, valamint hivatkoz�s ";
      if (extractAll) 
        result+=" a megfelel� n�vt�r dokument�ci�ra minden tagn�l:";
      else 
        result+=" a n�vterekre, amelynek tagjai:";
      return result;
    }
    /*! This is used in LaTeX as the title of the chapter with the 
     *  index of all namespaces.
     */
    virtual QCString trNamespaceIndex()
    { return "N�vt�rmutat�"; }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all namespaces.
     */
    virtual QCString trNamespaceDocumentation()
    { return "N�vterek dokument�ci�ja"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990522
//////////////////////////////////////////////////////////////////////////

    /*! This is used in the documentation before the list of all
     *  namespaces in a file.
     */
    virtual QCString trNamespaces()
    { return "N�vterek"; }

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
      QCString result=(QCString)"Ez a dokument�ci� ";
      switch(compType)
      {
        case ClassDef::Class:      result+="az oszt�lyr�l"; break;
        case ClassDef::Struct:     result+="a strukt�r�r�l"; break;
        case ClassDef::Union:      result+="az uni�r�l"; break;
        case ClassDef::Interface:  result+="az interf�szr�l"; break;
        case ClassDef::Protocol:   result+="protocol"; break; // translate me!
        case ClassDef::Category:   result+="category"; break; // translate me!
        case ClassDef::Exception:  result+="a kiv�telr�l"; break;
      }
      result+=" a k�vetkez� f�jl";
      if (!single) result+="ok";
      result+=" alapj�n k�sz�lt:";
      return result;
    }

    /*! This is in the (quick) index as a link to the alphabetical compound
     * list.
     */
    virtual QCString trAlphabeticalList()
    { return "Bet�rendes lista"; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990901
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the heading text for the retval command. */
    virtual QCString trReturnValues()
    { return "Visszat�r�si �rt�kek"; }

    /*! This is in the (quick) index as a link to the main page (index.html)
     */
    virtual QCString trMainPage()
    { return "F�oldal"; }

    /*! This is used in references to page that are put in the LaTeX 
     *  documentation. It should be an abbreviation of the word page.
     */
    virtual QCString trPageAbbreviation()
    { return "o."; }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991003
//////////////////////////////////////////////////////////////////////////

    virtual QCString trDefinedAtLineInSourceFile()
    {
      return "Defin�ci� a(z) @1 f�jl @0. sor�ban.";
    }
    virtual QCString trDefinedInSourceFile()
    {
      return "Defin�ci� a(z) @0 f�jlban.";
    }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991205
//////////////////////////////////////////////////////////////////////////

    virtual QCString trDeprecated()
    {
      return "Ellenjavallt";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.0.0
//////////////////////////////////////////////////////////////////////////

    /*! this text is put before a collaboration diagram */
    virtual QCString trCollaborationDiagram(const char *clName)
    {
      return (QCString)"A"+zed(clName[0])+clName+" oszt�ly egy�ttm�k�d�si diagramja:";
    }
    /*! this text is put before an include dependency graph */
    virtual QCString trInclDepGraph(const char *fName)
    {
      return (QCString)"A"+zed(fName[0])+fName+" defin�ci�s f�jl f�gg�si gr�fja:";
    }
    /*! header that is put before the list of constructor/destructors. */
    virtual QCString trConstructorDocumentation()
    {
      return "Konstruktorok �s destruktorok dokument�ci�ja"; 
    }
    /*! Used in the file documentation to point to the corresponding sources. */
    virtual QCString trGotoSourceCode()
    {
      return "Ugr�s a f�jl forr�sk�dj�hoz.";
    }
    /*! Used in the file sources to point to the corresponding documentation. */
    virtual QCString trGotoDocumentation()
    {
      return "Ugr�s a f�jl dokument�ci�j�hoz.";
    }
    /*! Text for the \\pre command */
    virtual QCString trPrecondition()
    {
      return "El�felt�tel";
    }
    /*! Text for the \\post command */
    virtual QCString trPostcondition()
    {
      return "Ut�felt�tel";
    }
    /*! Text for the \\invariant command */
    virtual QCString trInvariant()
    {
      return "Invari�ns";
    }
    /*! Text shown before a multi-line variable/enum initialization */
    virtual QCString trInitialValue()
    {
      return "Kezd� �rt�k:";
    }
    /*! Text used the source code in the file index */
    virtual QCString trCode()
    {
      return "forr�sk�d";
    }
    virtual QCString trGraphicalHierarchy()
    {
      return "Oszt�lyhierarchia-�bra";
    }
    virtual QCString trGotoGraphicalHierarchy()
    {
      return "Ugr�s az oszt�lyhierarchia-�br�hoz";
    }
    virtual QCString trGotoTextualHierarchy()
    {
      return "Ugr�s az sz�veges oszt�lyhierarchi�hoz";
    }
    virtual QCString trPageIndex()
    {
      return "Oldalmutat�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.0
//////////////////////////////////////////////////////////////////////////
    
    virtual QCString trNote()
    {
      return "Megjegyz�s";
    }
    virtual QCString trPublicTypes()
    {
      return "Publikus t�pusok";
    }
    virtual QCString trPublicAttribs()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Adatmez�k";
      }
      else
      {
        return "Publikus attrib�tumok";
      }
    }
    virtual QCString trStaticPublicAttribs()
    {
      return "Statikus publikus attrib�tumok";
    }
    virtual QCString trProtectedTypes()
    {
      return "V�dett t�pusok";
    }
    virtual QCString trProtectedAttribs()
    {
      return "V�dett attrib�tumok";
    }
    virtual QCString trStaticProtectedAttribs()
    {
      return "Statikus v�dett attrib�tumok";
    }
    virtual QCString trPrivateTypes()
    {
      return "Priv�t t�pusok";
    }
    virtual QCString trPrivateAttribs()
    {
      return "Priv�t attrib�tumok";
    }
    virtual QCString trStaticPrivateAttribs()
    {
      return "Statikus priv�t attrib�tumok";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a todo item */
    virtual QCString trTodo()
    {
      return "Tennival�";
    }
    /*! Used as the header of the todo list */
    virtual QCString trTodoList()
    {
      return "Tennival�k list�ja";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.4
//////////////////////////////////////////////////////////////////////////

    virtual QCString trReferencedBy()
    {
      return "Hivatkoz�sok:";
    }
    virtual QCString trRemarks()
    {
      return "Megjegyz�sek";
    }
    virtual QCString trAttention()
    {
      return "Figyelem";
    }
    virtual QCString trInclByDepGraph()
    {
      return "Ez az �bra azt mutatja, hogy mely f�jlok �gyazz�k be "
             "k�zvetve vagy k�zvetlen�l ezt a f�jlt:";
    }
    virtual QCString trSince()
    {
      return "El�sz�r bevezetve";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.1.5
//////////////////////////////////////////////////////////////////////////

    /*! title of the graph legend page */
    virtual QCString trLegendTitle()
    {
      return "Jelmagyar�zat";
    }
    /*! page explaining how the dot graph's should be interpreted */
    virtual QCString trLegendDocs()
    {
      return 
        "Ez az oldal elmagyar�zza hogyan kell �rtelmezni a "
        "doxygen �ltal k�sz�tett �br�kat.<p>\n"
        "Vegy�k a k�vetkez� p�ld�t:\n"
        "\\code\n"
        "/*! V�g�s miatt nem l�that� oszt�ly */\n"
        "class Invisible { };\n\n"
        "/*! Lev�gott oszt�ly, sz�rmaz�sa rejtett */\n"
        "class Truncated : public Invisible { };\n\n"
        "/* Doxygen kommentekkel nem dokument�lt oszt�ly */\n"
        "class Undocumented { };\n\n"
        "/*! Publikus sz�rmaztat�sal levezetett oszt�ly */\n"
        "class PublicBase : public Truncated { };\n\n"
        "/*! Egy sablonoszt�ly */\n"
        "template<class T> class Templ { };\n\n"
        "/*! V�dett sz�rmaztat�sal levezetett oszt�ly */\n"
        "class ProtectedBase { };\n\n"
        "/*! Priv�t sz�rmaztat�sal levezetett oszt�ly */\n"
        "class PrivateBase { };\n\n"
        "/*! Oszt�ly, melyet a sz�rmaztatott oszt�ly haszn�l */\n"
        "class Used { };\n\n"
        "/*! Oszt�ly, mely t�bb m�siknak lesz�rmazottja */\n"
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
        "Ha a konfigur�ci�s f�jl \\c MAX_DOT_GRAPH_HEIGHT elem�nek �rt�k�t "
        "240-re �ll�tjuk, az eredm�ny a k�vetkez� �bra lesz:"
        "<p><center><img src=\"graph_legend."+Config_getEnum("DOT_IMAGE_FORMAT")+"\"></center>\n"
        "<p>\n"
        "Az �br�n lev� dobozok jelent�se:\n"
        "<ul>\n"
        "<li>Kit�lt�tt fekete doboz jelzi azt az oszt�lyt vagy strukt�r�t,"
        "amelyr�l az �bra sz�l.\n"
        "<li>Fekete keret jelzi a dokument�lt oszt�lyokat �s strukt�r�kat.\n"
        "<li>Sz�rke keret jelzi a nem dokument�lt oszt�lyokat �s strukt�r�kat.\n"
        "<li>Piros keret jelzi azokat az oszt�lyokat �s strukt�r�kat, amelyekn�l v�g�s miatt nem l�that� "
        "az �sszes lesz�rmaztat�si kapcsolat. Egy �bra v�g�sra ker�l, ha nem f�r bele "
        "a megadott tartom�nyba."
        "</ul>\n"
        "A nyilak jelent�se:\n"
        "<ul>\n"
        "<li>S�t�tk�k ny�l jelzi a publikus sz�rmaztat�st.\n"
        "<li>S�t�tz�ld ny�l jelzi a v�dett sz�rmaztat�st.\n"
        "<li>S�t�tv�r�s ny�l jelzi a priv�t sz�rmaztat�st.\n"
        "<li>Lila szaggatott ny�l jelzi, ha az oszt�ly egy m�sikat haszn�l vagy tartalmaz. "
        "A ny�l felirata jelzi a v�ltoz�(k) nev�t, amelyeken kereszt�l a m�sik oszt�ly kapcsol�dik.\n"
        "<li>S�rga szaggatott ny�l jelzi a kapcsolatot a sablonp�ld�ny �s a p�ld�nyos�tott "
        "oszt�lysablon k�z�tt. A ny�l felirata jelzi a p�l�ny sablonparam�tereit.\n"
        "</ul>\n";

    }
    /*! text for the link to the legend page */
    virtual QCString trLegend()
    {
      return "Jelmagyar�zat";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.2.0
//////////////////////////////////////////////////////////////////////////
    
    /*! Used as a marker that is put before a test item */
    virtual QCString trTest()
    {
      return "Teszt";
    }
    /*! Used as the header of the test list */
    virtual QCString trTestList()
    {
      return "Tesztlista";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.1
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for KDE-2 IDL methods */
    virtual QCString trDCOPMethods()
    {
      return "DCOP tagf�ggv�nyek";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.2
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for IDL properties */
    virtual QCString trProperties()
    {
      return "Tulajdons�gok";
    }
    /*! Used as a section header for IDL property documentation */
    virtual QCString trPropertyDocumentation()
    {
      return "Tulajdons�gok dokument�ci�jka";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.4
//////////////////////////////////////////////////////////////////////////

    /*! Used for Java classes in the summary section of Java packages */
    virtual QCString trClasses()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return "Adatszerkezetek";
      }
      else
      {
        return "Oszt�lyok";
      }
    }
    /*! Used as the title of a Java package */
    virtual QCString trPackage(const char *name)
    {
      return name+(QCString)" csomag";
    }
    /*! Title of the package index page */
    virtual QCString trPackageList()
    {
      return "Csomaglista";
    }
    /*! The description of the package index page */
    virtual QCString trPackageListDescription()
    {
      return "A csomagok r�vid le�r�sai (amennyiben l�teznek):";
    }
    /*! The link name in the Quick links header for each page */
    virtual QCString trPackages()
    {
      return "Csomagok";
    }
    /*! Text shown before a multi-line define */
    virtual QCString trDefineValue()
    {
      return "�rt�k:";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.2.5
//////////////////////////////////////////////////////////////////////////
    
    /*! Used as a marker that is put before a \\bug item */
    virtual QCString trBug()
    {
      return "Hiba";
    }
    /*! Used as the header of the bug list */
    virtual QCString trBugList()
    {
      return "Hiba lista";
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
      return "1250";
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
      return "T�rgymutat�";
    }
   
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trClass(bool first_capital, bool /*singular*/)
    { 
      QCString result((first_capital ? "Oszt�ly" : "oszt�ly"));
      //if (!singular)  result+="es";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trFile(bool first_capital, bool /*singular*/)
    { 
      QCString result((first_capital ? "F�jl" : "f�jl"));
      //if (!singular)  result+="s";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trNamespace(bool first_capital, bool /*singular*/)
    { 
      QCString result((first_capital ? "N�vt�r" : "n�vt�r"));
      //if (!singular)  result+="s";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trGroup(bool first_capital, bool /*singular*/)
    { 
      QCString result((first_capital ? "Csoport" : "csoport"));
      //if (!singular)  result+="s";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trPage(bool first_capital, bool /*singular*/)
    { 
      QCString result((first_capital ? "Oldal" : "oldal"));
      //if (!singular)  result+="s";
      return result; 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trMember(bool first_capital, bool /*singular*/)
    { 
      QCString result((first_capital ? "Tag" : "tag"));
      //if (!singular)  result+="s";
      return result; 
    }
   
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trGlobal(bool first_capital, bool /*singular*/)
    { 
      QCString result((first_capital ? "Glob�lis elem" : "glob�lis elem"));
      //if (!singular)  result+="s";
      return result; 
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.7
//////////////////////////////////////////////////////////////////////////

    /*! This text is generated when the \\author command is used and
     *  for the author section in man pages. */
    virtual QCString trAuthor(bool first_capital, bool singular)
    {                                                                         
      QCString result((first_capital ? "Szerz�" : "szerz�"));
      if (!singular)  result+="k";
      return result; 
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.11
//////////////////////////////////////////////////////////////////////////

    /*! This text is put before the list of members referenced by a member
     */
    virtual QCString trReferences()
    {
      return "Hivatkoz�sok";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.13
//////////////////////////////////////////////////////////////////////////

    /*! used in member documentation blocks to produce a list of 
     *  members that are implemented by this one.
     */
    virtual QCString trImplementedFromList(int numEntries)
    {
      return "Megval�s�tja a k�vetkez�ket: "+trWriteList(numEntries)+".";
    }

    /*! used in member documentation blocks to produce a list of
     *  all members that implement this abstract member.
     */
    virtual QCString trImplementedInList(int numEntries)
    {
      return "Megval�s�tj�k a k�vetkez�k: "+trWriteList(numEntries)+".";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.16
//////////////////////////////////////////////////////////////////////////

    /*! used in RTF documentation as a heading for the Table
     *  of Contents.
     */
    virtual QCString trRTFTableOfContents()
    {
      return "Tartalomjegyz�k";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.17
//////////////////////////////////////////////////////////////////////////

    /*! Used as the header of the list of item that have been 
     *  flagged deprecated 
     */
    virtual QCString trDeprecatedList()
    {
      return "Ellenjavallt elemek list�ja";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.18
//////////////////////////////////////////////////////////////////////////

    /*! Used as a header for declaration section of the events found in 
     * a C# program
     */
    virtual QCString trEvents()
    {
      return "Esem�nyek";
    }
    /*! Header used for the documentation section of a class' events. */
    virtual QCString trEventDocumentation()
    {
      return "Esem�nyek dokument�ci�ja";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a heading for a list of Java class types with package scope.
     */
    virtual QCString trPackageTypes()
    { 
      return "Csomag t�pusok";
    }
    /*! Used as a heading for a list of Java class functions with package 
     * scope. 
     */
    virtual QCString trPackageMembers()
    { 
      return "Csomag f�ggv�nyek";
    }
    /*! Used as a heading for a list of static Java class functions with 
     *  package scope.
     */
    virtual QCString trStaticPackageMembers()
    { 
      return "Statikus csomag f�ggv�nyek";
    }
    /*! Used as a heading for a list of Java class variables with package 
     * scope.
     */
    virtual QCString trPackageAttribs()
    { 
      return "Csomag attrib�tumok";
    }
    /*! Used as a heading for a list of static Java class variables with 
     * package scope.
     */
    virtual QCString trStaticPackageAttribs()
    { 
      return "Statikus csomag attrib�tumok";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.3.1
//////////////////////////////////////////////////////////////////////////

    /*! Used in the quick index of a class/file/namespace member list page 
     *  to link to the unfiltered list of all members.
     */
    virtual QCString trAll()
    {
      return "�sszes";
    }
    /*! Put in front of the call graph for a function. */
    virtual QCString trCallGraph()
    {
      return "A f�ggv�ny h�v�si gr�fja:";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.3
//////////////////////////////////////////////////////////////////////////

    /*! When the search engine is enabled this text is put in the header 
     *  of each page before the field where one can enter the text to search 
     *  for. 
     */
    virtual QCString trSearchForIndex()
    {
      return "Keres�si kulcs";
    }
    /*! This string is used as the title for the page listing the search
     *  results.
     */
    virtual QCString trSearchResultsTitle()
    {
      return "A keres�s eredm�nye";
    }
    /*! This string is put just before listing the search results. The
     *  text can be different depending on the number of documents found.
     *  Inside the text you can put the special marker $num to insert
     *  the number representing the actual number of search results.
     *  The @a numDocuments parameter can be either 0, 1 or 2, where the 
     *  value 2 represents 2 or more matches. HTML markup is allowed inside
     *  the returned string.
     */
    virtual QCString trSearchResults(int numDocuments)
    {
      if (numDocuments==0)
      {
        return "Sajnos egy dokumentum sem felelt meg a keres�si felt�teleknek.";
      }
      else if (numDocuments==1)
      {
        return "<b>1</b> dokumentum felelt meg a keres�si felt�teleknek.";
      }
      else 
      {
        return "<b>$num</b> dokumentum felelt meg a keres�si felt�teleknek."
               "Els�nek a legjobb tal�latok vannak felt�ntetve.";
      }
    }
    /*! This string is put before the list of matched words, for each search 
     *  result. What follows is the list of words that matched the query.
     */
    virtual QCString trSearchMatches()
    {
      return "Tal�latok:";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.8
//////////////////////////////////////////////////////////////////////////

    /*! This is used in HTML as the title of page with source code for file filename
     */
    virtual QCString trSourceFile(QCString& filename)
    {
      return filename + " Forr�sf�jl";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.9
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the name of the chapter containing the directory
     *  hierarchy.
     */
    virtual QCString trDirIndex()
    { return "K�nyvt�rhierarchia"; }

    /*! This is used as the name of the chapter containing the documentation
     *  of the directories.
     */
    virtual QCString trDirDocumentation()
    { return "K�nyvt�rak dokument�ci�ja"; }

    /*! This is used as the title of the directory index and also in the
     *  Quick links of a HTML page, to link to the directory hierarchy.
     */
    virtual QCString trDirectories()
    { return "K�nyvt�rak"; }

    /*! This returns a sentences that introduces the directory hierarchy. 
     *  and the fact that it is sorted alphabetically per level
     */
    virtual QCString trDirDescription()
    { return "Majdnem (de nem teljesen) bet�rendbe szedett "
             "k�nyvt�rhierarchia:";
    }

    /*! This returns the title of a directory page. The name of the
     *  directory is passed via \a dirName.
     */
    virtual QCString trDirReference(const char *dirName)
    { QCString result=dirName; result+=" k�nyvt�rreferencia"; return result; }

    /*! This returns the word directory with or without starting capital
     *  (\a first_capital) and in sigular or plural form (\a singular).
     */
    virtual QCString trDir(bool first_capital, bool /*singular*/)
    { 
      QCString result((first_capital ? "K�nyvt�r" : "k�nyvt�r"));
      //if (singular) result+="y"; else result+="ies";
      return result; 
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.4.1
//////////////////////////////////////////////////////////////////////////

    /*! This text is added to the documentation when the \\overload command
     *  is used for a overloaded function.
     */
    virtual QCString trOverloadText()
    {
       return "Ez egy t�lterhelt tagf�ggv�ny."
              "A fenti f�ggv�nyt�l csak argumentumaiban k�l�nb�zik.";
    }
};

#endif
