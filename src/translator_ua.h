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
 * The translation into Ukrainian was provided by
 *   Olexij Tkatchenko (olexij.tkatchenko@parcs.de)
 */

#ifndef TRANSLATOR_UA_H
#define TRANSLATOR_UA_H

class TranslatorUkrainian : public TranslatorAdapter_1_4_1
{
  private:
    /*! The Decode() inline assumes the source written in the 
        Koi8-U encoding (maintainer dependent). 
     */
    inline QCString decode(const QCString & sInput)
    { 
//#ifdef _WIN32
//      return Koi8RToWindows1251(sInput);
//#else
      return sInput;
//#endif
    }

  public:
    /*! Used for identification of the language. */
    virtual QCString idLanguage()
    { return "ukrainian"; }

    /* Used to get the command(s) for the language support. */
    virtual QCString latexLanguageSupportCommand()
    {
//#ifdef _WIN32
//      return "\\usepackage[cp1251]{inputenc}\n\\usepackage[ukrainian]{babel}\n"; 
//#else
      return "\\usepackage[T2A]{fontenc}\n\\usepackage[ukrainian]{babel}\n"; 
//#endif
    }

    /*! return the language charset. This will be used for the HTML output */
    virtual QCString idLanguageCharset()
    {
//#ifdef _WIN32
//      return "Windows-1251"; 
//#else
      return "koi8-u";
//#endif
    }

    // --- Language translation methods -------------------

    /*! used in the compound documentation before a list of related functions. */
    virtual QCString trRelatedFunctions()
    { return decode("���Ҧ���Φ ���æ�"); }

    /*! subscript for the related functions. */
    virtual QCString trRelatedSubscript()
    { return decode("(�� ������ ���������)"); }

    /*! header that is put before the detailed description of files, classes and namespaces. */
    virtual QCString trDetailedDescription()
    { return decode("��������� ����"); }

    /*! header that is put before the list of typedefs. */
    virtual QCString trMemberTypedefDocumentation()
    { return decode("���� ��Ц� �����������"); }

    /*! header that is put before the list of enumerations. */
    virtual QCString trMemberEnumerationDocumentation()
    { return decode("���� ����̦˦� �����������"); }

    /*! header that is put before the list of member functions. */
    virtual QCString trMemberFunctionDocumentation()
    { return decode("���� ����Ħ� ���������"); }

    /*! header that is put before the list of member attributes. */
    virtual QCString trMemberDataDocumentation()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return decode( "����" );
      }
      else
      {
        return decode( "���������Φ ��Φ" );
      }
    }

    /*! this is the text of a link put after brief descriptions. */
    virtual QCString trMore()
    { return decode("������Φ��..."); }

    /*! put in the class documentation */
    /* Dosn't use when optimization for C is on. */
    virtual QCString trListOfAllMembers()
    {
      return decode( "������ �Ӧ� ������Ԧ�" );
    }

    /*! used as the title of the "list of all members" page of a class */
    /* Dosn't use when optimization for C is on. */
    virtual QCString trMemberList()
    {
      return decode( "C����� ������Ԧ�" );
    }

    /*! this is the first part of a sentence that is followed by a class name */
    /* Dosn't use when optimization for C is on. */
    virtual QCString trThisIsTheListOfAllMembers()
    { return decode("������ ������ ������Ԧ�"); }

    /*! this is the remainder of the sentence after the class name */
    /* Dosn't use when optimization for C is on. */
    virtual QCString trIncludingInheritedMembers()
    { return decode(", ��������� �Ӧ ���������Φ ��������"); }

    /*! this is put at the author sections at the bottom of man pages.
     *  parameter s is name of the project name.
     */
    virtual QCString trGeneratedAutomatically(const char *s)
    { QCString result=decode("����������� �������� �� ��������� Doxygen");
      if (s) result+=decode(" ��� ")+s;
      result+=decode(" � ������ ��������."); 
      return result;
    }

    /*! put after an enum name in the list of all members */
    virtual QCString trEnumName()
    { return decode("����̦�"); }

    /*! put after an enum value in the list of all members */
    virtual QCString trEnumValue()
    { return decode("������� ����̦��"); }

    /*! put after an undocumented member in the list of all members */
    virtual QCString trDefinedIn()
    { return decode("��������� � "); }

    // quick reference sections

    /*! This is put above each page as a link to the list of all groups of 
     *  compounds or files (see the \\group command).
     */
    virtual QCString trModules()
    { return decode("�������Φ ����̦"); }

    /*! This is put above each page as a link to the class hierarchy */
    virtual QCString trClassHierarchy()
    { return decode("�����Ȧ� ���Ӧ�"); }

    /*! This is put above each page as a link to the list of annotated classes */
    virtual QCString trCompoundList()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return decode( "��������� �����" );
      }
      else
      {
        return decode( "�����" );
      }
    }

    /*! This is put above each page as a link to the list of documented files */
    virtual QCString trFileList()
    { return decode("�����"); }

    /*! This is put above each page as a link to the list of all verbatim headers */
    virtual QCString trHeaderFiles()
    { return decode("���������Φ �����"); }

    /*! This is put above each page as a link to all members of compounds. */
    virtual QCString trCompoundMembers()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return decode( "���� ��������" );
      }
      else
      {
        return decode( "�������� ���Ӧ�" );
      }
    }

    /*! This is put above each page as a link to all members of files. */
    /*??*/
    virtual QCString trFileMembers()
    {
      return decode( "�������� �����" );
    }

    /*! This is put above each page as a link to all related pages. */
    virtual QCString trRelatedPages()
    /* ?? ������� �������� "��. �����: " ����� �������, �� �� � ���������,
     ��� � ������ ������. */
    { return decode("��������� �������æ�"); }

    /*! This is put above each page as a link to all examples. */
    virtual QCString trExamples()
    { return decode("��������"); }

    /*! This is put above each page as a link to the search engine. */
    virtual QCString trSearch()
    { return decode("�����"); }

    /*! This is an introduction to the class hierarchy. */
    virtual QCString trClassHierarchyDescription()
    { return decode("������ ����������� ������������ ��������� �� ����צ��"); }

    /*! This is an introduction to the list with all files. */
    virtual QCString trFileListDescription(bool extractAll)
    {
      QCString result="������ ������ ";
      if (!extractAll) result+="�������������� ";
      result+="���̦�.";
      return decode(result);
    }

    /*! This is an introduction to the annotated compound list. */
    virtual QCString trCompoundListDescription()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return decode( "��������� ����� � �������� ������." );
      }
      else
      {
        return decode( "�����, ���������, ��'������� �� ����������  � �������� ������." );
      }
    }

    /*! This is an introduction to the page with all class members. */
    virtual QCString trCompoundMembersDescription(bool extractAll)
    {
        QCString result="������ �Ӧ� ";
        if(!extractAll) result+="������������� ";
        if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
          result+="������Ԧ� �������� ����� � ���������� �� ";
        else
          result+="������Ԧ� ���Ӧ� ����� � ���������� �� ";
        if(extractAll)
        {
          if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
            result+="���������æ� �� �������Ҧ/��'������� ������� ��������.";
          else
            result+="���������æ� �� ����� ������� ��������.";
        }
        else
        {
          if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
            result += "צ���צ�Φ ���������";
          else
            result += "צ���צ�Φ �����";
          result+=", �� ���� ���� ��������.";
        }
        return decode( result );
    }

    /*! This is an introduction to the page with all file members. */
    virtual QCString trFileMembersDescription(bool extractAll)
    {
      QCString result="������ �Ӧ� ";
      if (!extractAll) result+="�������������� ";

      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        result+="����æ�, �ͦ����, �������������, "
                "����̦˦� � �������� ��Ц�";
      }
      else
      {
        result+="������Ԧ� ���̦� ";
      }
      result+=" � ��������� �� ";
      if (extractAll)
        result+="�����, �� ���� ���� ��������.";
      else
        result+="���������æ�.";
      return decode( result );
    }

    /*! This is an introduction to the page with the list of all header files. */
    virtual QCString trHeaderFilesDescription()
    { return decode("������ ������ ������������ ���̦�."); }

    /*! This is an introduction to the page with the list of all examples */
    virtual QCString trExamplesDescription()
    { return decode("������ ������ ������Ħ�."); }

    /*! This is an introduction to the page with the list of related pages */
    virtual QCString trRelatedPagesDescription()
    { return decode("������ ������ ���������� ���Ӧ�."); }

    /*! This is an introduction to the page with the list of class/file groups */
    virtual QCString trModulesDescription()
    { return decode("������ ������ ����̦�."); }

    /*! This sentences is used in the annotated class/file lists if no brief
     * description is given. 
     */
    virtual QCString trNoDescriptionAvailable()
    { return decode("���� צ����Φ�"); }

    // index titles (the project name is prepended for these) 


    /*! This is used in HTML as the title of index.html. */
    virtual QCString trDocumentation()
    { return decode("���������æ�"); }

    /*! This is used in LaTeX as the title of the chapter with the 
     * index of all groups.
     */
    virtual QCString trModuleIndex()
    { return decode("����צ���� �������� ����̦�"); }

    /*! This is used in LaTeX as the title of the chapter with the 
     * class hierarchy.
     */
    virtual QCString trHierarchicalIndex()
    { return decode("�����Ȧ���� �������� ���Ӧ�"); }

    /*! This is used in LaTeX as the title of the chapter with the 
     * annotated compound index.
     */
    virtual QCString trCompoundIndex()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return decode( "����צ���� �������� �������� �����" );
      }
      else
      {
        return decode( "����צ���� �������� ���Ӧ�" );
      }
    }

    /*! This is used in LaTeX as the title of the chapter with the
     * list of all files.
     */
    virtual QCString trFileIndex()
    { return decode( "�������� �����" ); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all groups.
     */
    virtual QCString trModuleDocumentation()
    { return decode("�������Φ ����̦"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all classes, structs and unions.
     */
    virtual QCString trClassDocumentation()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return decode( "��������� �����" );
      }
      else
      {
        return decode( "�����" );
      }
    }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all files.
     */
    virtual QCString trFileDocumentation()
    { return decode("�����"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all examples.
     */
    virtual QCString trExampleDocumentation()
    { return decode("��������"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all related pages.
     */
    virtual QCString trPageDocumentation()
    { return decode("���������æ� �� ��ͦ"); }

    /*! This is used in LaTeX as the title of the document */
    virtual QCString trReferenceManual()
    { return decode("��צ������ ��Ӧ����"); }

    /*! This is used in the documentation of a file as a header before the 
     *  list of defines
     */
    virtual QCString trDefines()
    { return decode("��������������"); }

    /*! This is used in the documentation of a file as a header before the 
     *  list of function prototypes
     */
    virtual QCString trFuncProtos()
    { return decode("��������� ���æ�"); }

    /*! This is used in the documentation of a file as a header before the 
     *  list of typedefs
     */
    virtual QCString trTypedefs()
    { return decode("��������� ��Ц�"); }

    /*! This is used in the documentation of a file as a header before the 
     *  list of enumerations
     */
    virtual QCString trEnumerations()
    { return decode("����̦��"); }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) functions
     */
    virtual QCString trFunctions()
    { return decode("����æ�"); }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) variables
     */
    virtual QCString trVariables()
    { return decode("�ͦ�Φ"); }

    /*! This is used in the documentation of a file as a header before the 
     *  list of (global) variables
     */
    virtual QCString trEnumerationValues()
    { return decode("�������� ����̦˦�"); }

    /*! This is used in the documentation of a file before the list of
     *  documentation blocks for defines
     */
    virtual QCString trDefineDocumentation()
    { return decode("���� �������������"); }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for function prototypes
     */
    virtual QCString trFunctionPrototypeDocumentation()
    { return decode("���� �������Ц� ����æ�"); }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for typedefs
     */
    virtual QCString trTypedefDocumentation()
    { return decode("���� �������� ��Ц�"); }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for enumeration types
     */
    virtual QCString trEnumerationTypeDocumentation()
    { return decode("���� ����̦˦�"); }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for enumeration values
     */
    virtual QCString trEnumerationValueDocumentation()
    { return decode("���� ������Ԧ� ����̦��"); }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for functions
     */
    virtual QCString trFunctionDocumentation()
    { return decode("���� ����æ�"); }

    /*! This is used in the documentation of a file/namespace before the list 
     *  of documentation blocks for variables
     */
    virtual QCString trVariableDocumentation()
    { return decode("���� �ͦ����"); }

    /*! This is used in the documentation of a file/namespace/group before 
     *  the list of links to documented compounds
     */
    virtual QCString trCompounds()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return decode( "��������� �����" );
      }
      else
      { 
        return decode( "�����" );
      }

    }

    /*! This is used in the documentation of a group before the list of 
     *  links to documented files
     */
    /*! This is used in the standard footer of each page and indicates when 
     *  the page was generated 
     */
    virtual QCString trGeneratedAt(const char *date,const char *projName)
    { 
      QCString result=decode("���������æ� ");
      if (projName) result+=decode("�� ")+projName;
      result+=decode(" �������� ")+date;
      result+=decode(" ��������");
      return result;
    }
    /*! This is part of the sentence used in the standard footer of each page.
     */
    virtual QCString trWrittenBy()
    {
      return decode("�����:");
    }

    /*! this text is put before a class diagram */
    virtual QCString trClassDiagram(const char *clName)
    {
      return decode("����� ����������� ��� ")+clName;
    }

    /*! this text is generated when the \\internal command is used. */
    virtual QCString trForInternalUseOnly()
    { return decode("������ ��� ����Ҧ������ ������������"); }

    /*! this text is generated when the \\reimp command is used. */
    virtual QCString trReimplementedForInternalReasons()
    /*??*/
    { return decode("�ͦ���� � ����Ҧ�Φ� ������. �ͦ�� �� ���������� API."); 
    }

    /*! this text is generated when the \\warning command is used. */
    virtual QCString trWarning()
    { return decode("������������"); }

    /*! this text is generated when the \\bug command is used. */
    virtual QCString trBugsAndLimitations()
    { return decode("������� �� ��������� ������������"); }

    /*! this text is generated when the \\version command is used. */
    virtual QCString trVersion()
    { return decode("���Ӧ�"); }

    /*! this text is generated when the \\date command is used. */
    virtual QCString trDate()
    { return decode("����"); }

    /*! this text is generated when the \\return command is used. */
    virtual QCString trReturns()
    { return decode("��������"); }

    /*! this text is generated when the \\sa command is used. */
    virtual QCString trSeeAlso()
    { return decode("���. �����"); }

    /*! this text is generated when the \\param command is used. */
    virtual QCString trParameters()
    { return decode("���������"); }

    /*! this text is generated when the \\exception command is used. */
    virtual QCString trExceptions()
    { return decode("������� ���������� �����æ�"); }

    /*! this text is used in the title page of a LaTeX document. */
    virtual QCString trGeneratedBy()
    { return decode("�������� ��������"); }
    
//////////////////////////////////////////////////////////////////////////
// new since 0.49-990307 
//////////////////////////////////////////////////////////////////////////
    
    /*! used as the title of page containing all the index of all namespaces. */
    virtual QCString trNamespaceList()
    { return decode("����Ԧ� ����"); }

    /*! used as an introduction to the namespace list */
    virtual QCString trNamespaceListDescription(bool extractAll)
    {
      QCString result="������ ����̦� ";
      if (!extractAll) result+="�������������� ";
      result+="������Ҧ� ����.";
      return decode(result);
    }

    /*! used in the class documentation as a header before the list of all
     *  friends of a class
     */
    virtual QCString trFriends()
    { return decode("����Φ �����"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990405
//////////////////////////////////////////////////////////////////////////
    
    /*! used in the class documentation as a header before the list of all
     * related classes 
     */
    virtual QCString trRelatedFunctionDocumentation()
      { return decode("������������ �� ����Φ� ���Ӧ� �� צ���צ���� ����æ�"); }
    
//////////////////////////////////////////////////////////////////////////
// new since 0.49-990425
//////////////////////////////////////////////////////////////////////////

    /*! used as the title of the HTML page of a class/struct/union */
    virtual QCString trCompoundReference(const char *clName,
                                 ClassDef::CompoundType compType,
                                 bool isTemplate)
    {
      QCString result;
      if (isTemplate) 
      {
        result="������ ";
        switch(compType)
        {
          case ClassDef::Class:  result+="�����"; break;
          case ClassDef::Struct: result+="���������"; break;
          case ClassDef::Union:  result+="��'�������"; break;
          case ClassDef::Interface:  result+="����������"; break;
          case ClassDef::Protocol:   result+="���������"; break;
          case ClassDef::Category:   result+="������Ҧ�"; break;
          case ClassDef::Exception:  result+="�������"; break;
        }
      }
      else
      {
        switch(compType)
        {
          case ClassDef::Class:  result+="����"; break;
          case ClassDef::Struct: result+="���������"; break;
          case ClassDef::Union:  result+="��'�������"; break;
          case ClassDef::Interface:  result+="���������"; break;
          case ClassDef::Protocol:   result+="��������"; break;
          case ClassDef::Category:   result+="������Ҧ�"; break;
          case ClassDef::Exception:  result+="�������"; break;
        }
      }
      result+=" ";
      return decode(result)+clName;
    }

    /*! used as the title of the HTML page of a file */
    virtual QCString trFileReference(const char *fileName)
    {
      return decode("���� ")+fileName;
    }

    /*! used as the title of the HTML page of a namespace */
    virtual QCString trNamespaceReference(const char *namespaceName)
    {
      return decode("����Ԧ� ���� ")+namespaceName;
    }
    
    virtual QCString trPublicMembers()
    { return decode("��������������Φ ��������"); }
    virtual QCString trPublicSlots()
    { return decode("��������������Φ �����"); }
    virtual QCString trSignals()
    { return decode("�������"); }
    virtual QCString trStaticPublicMembers()
    { return decode("��������������Φ ������Φ ��������"); }
    virtual QCString trProtectedMembers()
    { return decode("������Φ ��������"); }
    virtual QCString trProtectedSlots()
    { return decode("������Φ �����"); }
    virtual QCString trStaticProtectedMembers()
    { return decode("������Φ ������Φ ��������"); }
    virtual QCString trPrivateMembers()
    { return decode("������Φ ��������"); }
    virtual QCString trPrivateSlots()
    { return decode("������Φ �����"); }
    virtual QCString trStaticPrivateMembers()
    { return decode("������Φ ������Φ ��������"); }
    
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
            result+=decode( " � " );
        }
      }
      return result; 
    }
    
    /*! used in class documentation to produce a list of base classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritsList(int numEntries)
    {
      return decode("��������դ ���� ")+trWriteList(numEntries)+".";
    }

    /*! used in class documentation to produce a list of super classes,
     *  if class diagrams are disabled.
     */
    virtual QCString trInheritedByList(int numEntries)
    {
      return decode("����������� ������� ")+trWriteList(numEntries)+".";
    }

    /*! used in member documentation blocks to produce a list of 
     *  members that are hidden by this one.
     */
    virtual QCString trReimplementedFromList(int numEntries)
    {
      return decode("������������� � ")+trWriteList(numEntries)+".";
    }

    /*! used in member documentation blocks to produce a list of
     *  all member that overwrite the implementation of this member.
     */
    virtual QCString trReimplementedInList(int numEntries)
    {
      return decode("��������������� � ")+trWriteList(numEntries)+".";
    }

    /*! This is put above each page as a link to all members of namespaces. */
    virtual QCString trNamespaceMembers()
    { return decode("�������� �������� ����"); }

    /*! This is an introduction to the page with all namespace members */
    virtual QCString trNamespaceMemberDescription(bool extractAll)
    {
      QCString result="������ ����̦� ";
      if (!extractAll) result+="�������������� ";
      result+="�����Ԧ� �������� ���� � ���������� ";
      if (extractAll) 
        result+="�� ���������æ� ��� ������� ��������:";
      else 
        result+="�� ����Ԧ� ���� �� ����� ���� ��������:";
      return decode(result);
    }

    /*! This is used in LaTeX as the title of the chapter with the 
     *  index of all namespaces.
     */
    virtual QCString trNamespaceIndex()
    { return decode("����צ���� �������� �������� ����"); }

    /*! This is used in LaTeX as the title of the chapter containing
     *  the documentation of all namespaces.
     */
    virtual QCString trNamespaceDocumentation()
    { return decode("���� �������� ����"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990522
//////////////////////////////////////////////////////////////////////////

    /*! This is used in the documentation before the list of all
     *  namespaces in a file.
     */
    virtual QCString trNamespaces()
    { return decode( "�������� ����" ); }

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
      QCString result=(QCString)"���������æ�  ";
      switch(compType)
      {
        case ClassDef::Class:
          if (single) result+="����� �����"; else result+="��� ���Ӧ�";
          break;
        case ClassDef::Struct:
          if (single) result+="æ�� ���������"; else result+="��� ��������";
          break;
        case ClassDef::Union:
          if (single) result+="����� ��'�������"; else result+="��� ��'������";
          break;
        case ClassDef::Interface:
          if (single) result+="����� ����������"; else result+="��� ��������Ӧ�";
          break;
        case ClassDef::Protocol:  
          if (single) result+="����� ���������"; else result+="��� �������̦�";
          break; 
        case ClassDef::Category:
          if (single) result+="æ�� ������Ҧ�"; else result+="��� ������Ҧ�";
          break; 
        case ClassDef::Exception:
          if (single) result+="����� �������"; else result+="��� �����˦�";
          break;
      }
      result+=" ���� �������� � ����";
      if (single) result+="�:"; else result+="��:";
      return decode(result);
    }

    /*! This is in the (quick) index as a link to the alphabetical compound
     * list.
     */
    virtual QCString trAlphabeticalList()
    { return decode("����צ���� ��������"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990901
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the heading text for the retval command. */
    virtual QCString trReturnValues()
    { return decode("��������, �� ������������"); }

    /*! This is in the (quick) index as a link to the main page (index.html)
     */
    virtual QCString trMainPage()
    { return decode("�������� ���Ҧ���"); }

    /*! This is used in references to page that are put in the LaTeX 
     *  documentation. It should be an abbreviation of the word page.
     */
    virtual QCString trPageAbbreviation()
    { return decode("����."); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991106
//////////////////////////////////////////////////////////////////////////

    virtual QCString trSources()
    {
      return decode("��Ȧ�Φ ������.");
    }
    virtual QCString trDefinedAtLineInSourceFile()
    {
      return decode("���. ��������� � ���̦ @1, ����� @0");
    }
    virtual QCString trDefinedInSourceFile()
    {
      return decode("���. ��������� � ���̦ @0");
    }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991205
//////////////////////////////////////////////////////////////////////////

    virtual QCString trDeprecated()
    {
      return decode("�� �������������");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.0.0
//////////////////////////////////////////////////////////////////////////

    /*! this text is put before a collaboration diagram */
    virtual QCString trCollaborationDiagram(const char *clName)
    {
      return (QCString)decode("������� ��'��˦� ����� ")+clName+":";
    }
    /*! this text is put before an include dependency graph */
    virtual QCString trInclDepGraph(const char *fName)
    {
      return decode("������� ��������� ������������ ���̦� ��� ")+fName+":";
    }
    /*! header that is put before the list of constructor/destructors. */
    virtual QCString trConstructorDocumentation()
    {
      return decode("�����������(�)"); 
    }
    /*! Used in the file documentation to point to the corresponding sources. */
    virtual QCString trGotoSourceCode()
    {
      return decode("���. ��Ȧ�Φ ������.");
    }
    /*! Used in the file sources to point to the corresponding documentation. */
    virtual QCString trGotoDocumentation()
    {
      return decode("���. ���������æ�.");
    }
    /*! Text for the \\pre command */
    virtual QCString trPrecondition()
    {
      return decode("����������");
    }
    /*! Text for the \\post command */
    virtual QCString trPostcondition()
    {
      return decode("���������");
    }
    /*! Text for the \\invariant command */
    virtual QCString trInvariant()
    {
      return decode("����Ҧ���");
    }
    /*! Text shown before a multi-line variable/enum initialization */
    virtual QCString trInitialValue()
    {
      return decode("�������צ ��������");
    }
    /*! Text used the source code in the file index */
    virtual QCString trCode()
    {
      return decode("��Ȧ�Φ ������");
    }
    virtual QCString trGraphicalHierarchy()
    {
      return decode("���Ʀ��� �����Ȧ� ���Ӧ�");
    }
    virtual QCString trGotoGraphicalHierarchy()
    {
      return decode("���. ���Ʀ��� �����Ȧ�");
    }
    virtual QCString trGotoTextualHierarchy()
    {
      return decode("���. �������� �����Ȧ�");
    }
    virtual QCString trPageIndex()
    {
      return decode("����צ���� �������� ���������� ���Ӧ�");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.0
//////////////////////////////////////////////////////////////////////////
    
    virtual QCString trNote()
    {
      return decode("�������");
    }
    virtual QCString trPublicTypes()
    {
      return decode("��������������Φ ����");
    }
    virtual QCString trPublicAttribs()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return decode( "���� �����" );
      }
      else
      {
        return decode( "��������������Φ ��������" );
      }
    }
    virtual QCString trStaticPublicAttribs()
    {
      return decode("������Φ ��������������Φ ���Φ");
    }
    virtual QCString trProtectedTypes()
    {
      return decode("������Φ ����");
    }
    virtual QCString trProtectedAttribs()
    {
      return decode("������Φ ��Φ");
    }
    virtual QCString trStaticProtectedAttribs()
    {
      return decode("������Φ ������Φ ��Φ");
    }
    virtual QCString trPrivateTypes()
    {
      return decode("������Φ ����");
    }
    virtual QCString trPrivateAttribs()
    {
      return decode("������Φ ��Φ");
    }
    virtual QCString trStaticPrivateAttribs()
    {
      return decode("������Φ ������Φ ��Φ");
    }


//////////////////////////////////////////////////////////////////////////
// new since 1.1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a marker that is put before a todo item */
    virtual QCString trTodo()
    /*??*/
    {
      return decode("����Ȧ��� �������");
    }
    /*! Used as the header of the todo list */
    virtual QCString trTodoList()
    /*??*/
    {
      return decode("����̦� �������");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.1.4
//////////////////////////////////////////////////////////////////////////

    virtual QCString trReferencedBy()
    {
      return decode("���������� �");
    }
    virtual QCString trRemarks()
    {
      return decode("����.");
    }
    virtual QCString trAttention()
    {
      return decode("�����");
    }
    virtual QCString trInclByDepGraph()
    {
      return decode("���� ���̦�, �˦ ��������� ��� ����:");
    }
    virtual QCString trSince()
    /*??*/
    {
      return decode("��������� �");
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.1.5
//////////////////////////////////////////////////////////////////////////

    /*! title of the graph legend page */
    virtual QCString trLegendTitle()
    {
      return decode("�������");
    }
    /*! page explaining how the dot graph's should be interpreted */
    virtual QCString trLegendDocs()
    {
      return decode( 
        "����������, �� ���������������� � ������.<p>\n"
        "���������� ��������� �������:\n"
        "\\code\n"
        "/*! ��������� ���� ����� �Ҧ����� */\n"
        "class Invisible { };\n\n"
        "/*! ��������� ����, צ�������� ������������ ��������� */\n"
        "class Truncated : public Invisible { };\n\n"
        "/* ���������������� ���� */\n"
        "class Undocumented { };\n\n"
        "/*! ���������������� ������������ */\n"
        "class PublicBase : public Truncated { };\n\n"
        "/*! A template class */\n"
        "template<class T> class Templ { };\n\n"
        "/*! �������� ������������ */\n"
        "class ProtectedBase { };\n\n"
        "/*! �������� ������������ */\n"
        "class PrivateBase { };\n\n"
        "/*! ����, �� ����������դ���� ������ Inherited */\n"
        "class Used { };\n\n"
        "/*! ����, �� ��������դ ��ۦ ����� */\n"
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
        "���� \\c MAX_DOT_GRAPH_HEIGHT � ���Ʀ����æ����� ���̦ "
        "����������� �� 200, ��������� ��������� ����:"
        "<p><center><img src=\"graph_legend."+Config_getEnum("DOT_IMAGE_FORMAT")+"\"></center>\n"
        "<p>\n"
        "������������ � ����� ���Ʀ ����� ��������� �ͦ��:\n"
        "<ul>\n"
        "<li>���������� ������ ����������� צ�������� ��������� ��� ����, "
        "��� ����� �������� ����.\n"
        "<li>����������� � ������ ����� צ�������� ������������� ��������� ��� ����.\n"
        "<li>����������� � Ӧ��� ����� צ�������� ��������������� ��������� ��� ����.\n"
        "<li>����������� � �������� ����� צ�������� ������������� ��������� ��� ����, ��� ����\n"
        " �� �Ӧ �Ц�צ�������� ������������/�ͦ��� ������Φ. ���� �Ҧ�����, "
        "���� צ� �� �ͦ������� � �����Φ ��֦."
        "</ul>\n"
        "��Ҧ��� ����� ��������� �ͦ��:\n"
        "<ul>\n"
        "<li>��������� ��Ҧ��� צ�������� צ�������� ������������������ ������������ "
        "ͦ� ����� �������.\n"
        "<li>����������� ��Ҧ��� ����������դ���� ��� ���������� ����������Φ.\n"
        "<li>������������ ��Ҧ��� ����������դ���� ��� ���������� ����������Φ.\n"
        "<li>�������� ��Ҧ��� ����������դ����, ���� ���� ͦ������� �"
        "������ ���Ӧ ��� ��� ����������դ����."
        "��Ҧ��� ������դ���� �ͦ����, "
        "����� ��� צ���������� ������ �� ������ϧ ��������� ��� �����. \n"
        "</ul>\n");
    }
    /*! text for the link to the legend page */
    virtual QCString trLegend()
    {
      return decode("���. �������");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.0
//////////////////////////////////////////////////////////////////////////
    
    /*! Used as a marker that is put before a test item */
    virtual QCString trTest()
    {
      return decode("����");
    }
    /*! Used as the header of the test list */
    virtual QCString trTestList()
    {
      return decode("����̦� ���Ԧ�");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.1
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for KDE-2 IDL methods */
    virtual QCString trDCOPMethods()
    {
      return decode("DCOP ������");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.2
//////////////////////////////////////////////////////////////////////////

    /*! Used as a section header for IDL properties */
    virtual QCString trProperties()
    {
      return decode("���������Ԧ");
    }
    /*! Used as a section header for IDL property documentation */
    virtual QCString trPropertyDocumentation()
    {
      return decode("������ ����̦� ������������");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.4
//////////////////////////////////////////////////////////////////////////

    /*! Used for Java interfaces in the summary section of Java packages */
    virtual QCString trInterfaces()
    {
      return decode("����������");
    }
    /*! Used for Java classes in the summary section of Java packages */
    virtual QCString trClasses()
    {
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        return decode( "��������� �����" );
      }
      else
      {
        return decode( "�����" );
      }
    }
    /*! Used as the title of a Java package */
    virtual QCString trPackage(const char *name)
    {
      return decode("����� ")+name;
    }
    /*! Title of the package index page */
    virtual QCString trPackageList()
    {
      return decode("������ ����̦� ����Ԧ�");
    }
    /*! The description of the package index page */
    virtual QCString trPackageListDescription()
    {
      return decode("������ ����̦� �������������� ����Ԧ�.");
    }
    /*! The link name in the Quick links header for each page */
    virtual QCString trPackages()
    {
      return decode("������");
    }
    /*! Used as a chapter title for Latex & RTF output */
    virtual QCString trPackageDocumentation()
    {
      return decode("���� ����Ԧ�");
    }
    /*! Text shown before a multi-line define */
    virtual QCString trDefineValue()
    {
      return decode("��������������:");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.5
//////////////////////////////////////////////////////////////////////////
    
    /*! Used as a marker that is put before a \\bug item */
    virtual QCString trBug()
    {
      return decode("������");
    }
    /*! Used as the header of the bug list */
    virtual QCString trBugList()
    {
      return decode("����̦� �����Ԧ�");
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.6
//////////////////////////////////////////////////////////////////////////
    /*! Used as ansicpg for RTF file */
    virtual QCString trRTFansicp()
    {
      return "1251";
    }
    /*! Used as ansicpg for RTF fcharset */
    virtual QCString trRTFCharSet()
    {
      return "204";
    }
    /*! Used as header RTF general index */
    virtual QCString trRTFGeneralIndex()
    {
      return decode("���������� ��������");
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trClass(bool first_capital, bool singular)
    { 
      if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
      {
        QCString result((first_capital ? "��������� �����" : "��������� �����"));
        return decode(result); 
      }
      else
      {
        QCString result((first_capital ? "����" : "����"));
        if(!singular) result+="�";
        return decode(result); 
      }
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trFile(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "����" : "����"));
      if (!singular)  result+="�";
      return decode(result); 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trNamespace(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "�����" : "�����"));
      result+=(singular?"�� ����":"��� ����");
      return decode(result); 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trGroup(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "����" : "����"));
      result+=(singular ? "�" : "�");
      return decode(result); 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trPage(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "���Ҧ��" : "���Ҧ��"));
      result+=(singular ? "�" : "�");
      return decode(result); 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trMember(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "�������" : "�������"));
      if (!singular)  result+="�";
      return decode(result); 
    }
   
    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trField(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "���" : "���"));
      result+=(singular ? "�" : "�");
      return decode(result); 
    }

    /*! This is used for translation of the word that will possibly
     *  be followed by a single name or by a list of names 
     *  of the category.
     */
    virtual QCString trGlobal(bool first_capital, bool singular)
    { 
      QCString result((first_capital ? "��������" : "��������"));
      result+=(singular ? "��" : "�");
      return decode(result); 
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.7
//////////////////////////////////////////////////////////////////////////

    /*! This text is generated when the \\author command is used and
     *  for the author section in man pages. */
    virtual QCString trAuthor(bool first_capital, bool singular)
    {                                                                         
      QCString result((first_capital ? "�����" : "�����"));
      if (!singular) result+="�";
      return decode(result); 
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.11
//////////////////////////////////////////////////////////////////////////

    /*! This text is put before the list of members referenced by a member
     */
    virtual QCString trReferences()
    {
      return "����������դ";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.13
//////////////////////////////////////////////////////////////////////////

    /*! used in member documentation blocks to produce a list of 
     *  members that are implemented by this one.
     */
    virtual QCString trImplementedFromList(int numEntries)
    {
      return "���̦�դ " + trWriteList(numEntries) + ".";
    }

    /*! used in member documentation blocks to produce a list of
     *  all members that implement this abstract member.
     */
    virtual QCString trImplementedInList(int numEntries)
    {
      return "���̦�դ � " + trWriteList(numEntries) + ".";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.16
//////////////////////////////////////////////////////////////////////////

    /*! used in RTF documentation as a heading for the Table
     *  of Contents.
     */
    virtual QCString trRTFTableOfContents()
    {
      return "�ͦ��";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.17
//////////////////////////////////////////////////////////////////////////

    /*! Used as the header of the list of item that have been 
     *  flagged deprecated 
     */
    virtual QCString trDeprecatedList()
    {
      return "�����Ҧ̦ ��������";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.2.18
//////////////////////////////////////////////////////////////////////////

    /*! Used as a header for declaration section of the events found in 
     * a C# program
     */
    virtual QCString trEvents()
    {
      return "��Ħ�";
    }

    /*! Header used for the documentation section of a class' events. */
    virtual QCString trEventDocumentation()
    {
      return "���������æ� ��Ħ�";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3
//////////////////////////////////////////////////////////////////////////

    /*! Used as a heading for a list of Java class types with package scope.
     */
    virtual QCString trPackageTypes()
    { 
      return "���� ����Ԧ�";
    }

    /*! Used as a heading for a list of Java class functions with package 
     * scope. 
     */
    virtual QCString trPackageMembers()
    { 
      return "����æ� ����Ԧ�";
    }

    /*! Used as a heading for a list of static Java class functions with 
     *  package scope.
     */
    virtual QCString trStaticPackageMembers()
    { 
      return "������Φ ����æ� ����Ԧ�";
    }
    
    /*! Used as a heading for a list of Java class variables with package 
     * scope.
     */
    virtual QCString trPackageAttribs()
    {
      return "�������� ����Ԧ�";
    }
    
    /*! Used as a heading for a list of static Java class variables with 
     * package scope.
     */
    virtual QCString trStaticPackageAttribs()
    {
      return "������Φ �������� ����Ԧ�";
    }
    
//////////////////////////////////////////////////////////////////////////
// new since 1.3.1
//////////////////////////////////////////////////////////////////////////

    /*! Used in the quick index of a class/file/namespace member list page 
     *  to link to the unfiltered list of all members.
     */
    virtual QCString trAll()
    {
      return "�Ӧ";
    }
    /*! Put in front of the call graph for a function. */
    virtual QCString trCallGraph()
    {
      return "���� �Ӧ� �����˦� æ�� ����æ�:";
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
      return "������";
    }
    /*! This string is used as the title for the page listing the search
     *  results.
     */
    virtual QCString trSearchResultsTitle()
    {
      return "���������� ������";
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
        return "�� �������� �������Ԧ� צ���צ��� �� ������ ������.";
      }
      else if (numDocuments==1)
      {
        return "���� �������� <b>1</b> �������� צ���צ��� �� ������ ������.";
      }
      else 
      {
        return "���� �������� <b>$num</b> �������Ԧ� צ���צ��� �� ������ ������. "
	       "������ݦ צ���צ����Ԧ �������� ��������.";
      }
    }
    /*! This string is put before the list of matched words, for each search 
     *  result. What follows is the list of words that matched the query.
     */
    virtual QCString trSearchMatches()
    {
      return "�����צ�Φ���:";
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.8
//////////////////////////////////////////////////////////////////////////

    /*! This is used in HTML as the title of page with source code for file filename
     */
    virtual QCString trSourceFile(QCString& filename)
    {
      return "����� �������� "+filename;
    }

//////////////////////////////////////////////////////////////////////////
// new since 1.3.9
//////////////////////////////////////////////////////////////////////////

    /*! This is used as the name of the chapter containing the directory
     *  hierarchy.
     */
    virtual QCString trDirIndex()
    { return "������ ������Ǧ�"; }

    /*! This is used as the name of the chapter containing the documentation
     *  of the directories.
     */
    virtual QCString trDirDocumentation()
    { return "���������æ� ������Ǧ�"; }

    /*! This is used as the title of the directory index and also in the
     *  Quick links of a HTML page, to link to the directory hierarchy.
     */
    virtual QCString trDirectories()
    { return "��������"; }

    /*! This returns a sentences that introduces the directory hierarchy. 
     *  and the fact that it is sorted alphabetically per level
     */
    virtual QCString trDirDescription()
    { return "������ ������Ǧ� ������������ ��������� "
	     "�� ����צ��:";
    }

    /*! This returns the title of a directory page. The name of the
     *  directory is passed via \a dirName.
     */
    virtual QCString trDirReference(const char *dirName)
    { QCString result="��צ���� �������� "; result+=dirName; return result; }

    /*! This returns the word directory with or without starting capital
     *  (\a first_capital) and in sigular or plural form (\a singular).
     */
    virtual QCString trDir(bool, bool singular)
    { 
      QCString result("�������");
      if (!singular) result+="�";
      return result; 
    }

};

#endif

