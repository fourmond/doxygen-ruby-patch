/******************************************************************************
 * <notice>This is the template for generating language.doc.  
 * Edit manually this file, not the language.doc!</notice>
 * 
 *
 * Copyright (C) 1997-2002 by Dimitri van Heesch.
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
/*! \page langhowto Internationalization

<h3>Support for multiple languages</h3>

Doxygen has built-in support for multiple languages. This means 
that the text fragments that doxygen generates can be produced in
languages other than English (the default) at configuration time.

Currently (version $version), $numlang languages 
are supported (sorted alphabetically): 
$languages.

The table of information related to the supported languages follows.
It is sorted by language alphabetically.  The <b>Status</b> column
was generated from sources and shows approximately the last version
when the translator was updated.

$information_table

Most people on the list have indicated that they were also busy
doing other things, so if you want to help to speed things up please 
let them (or me) know.

If you want to add support for a language that is not yet listed 
please read the next section.


<h3>Adding a new language to doxygen</h3>

This short HOWTO explains how to add support for a new language to Doxygen:

Just follow these steps:
<ol>
<li>Tell me for which language you want to add support. If no one else
    is already working on support for that language, you will be 
    assigned as the maintainer for the language. 
<li>Create a copy of translator_en.h and name it 
    translator_<your_2_letter_country_code>.h
    I'll use xx in the rest of this document.
<li>Edit language.cpp:
    Add a 
\verbatim
#include<translator_xx.h>
\endverbatim
    in <code>setTranslator()</code> add
\verbatim
    else if (L_EQUAL("your_language_name"))
    {
      theTranslator = new TranslatorYourLanguage;
    }
\endverbatim
    after the <code>if { ... }</code>
<li>Edit libdoxygen.pro.in and add \c translator_xx.h to 
    the \c HEADERS line.
<li>Edit <code>translator_xx.h</code>:
   <ul>
   <li>Rename <code>TRANSLATOR_EN_H</code> to <code>TRANSLATOR_XX_H</code> twice.
   <li>Rename TranslatorEnglish to TranslatorYourLanguage 
   <li>In the member <code>idLanguage()</code> change "english" into the 
     name of your language (use lower case characters only). Depending
     on the language you may also wish to change the member functions 
     latexLanguageSupportCommand(), idLanguageCharset() and others
     (you will recognize them when you start the work).
   <li>Edit all the strings that are returned by the member functions that 
     start with tr. 
     Try to match punctuation and capitals!
     To enter special characters (with accents) you can:
     <ul>
     <li>  Enter them directly if your keyboard supports that and you are 
           using a Latin-1 font. Doxygen will translate the
           characters to proper \f$\mbox{\LaTeX}\f$ and leave the
           HTML and man output for what it is (which is fine, if
           idLanguageCharset() is set correctly).
     <li>  Use html codes like \&auml; for an a with an umlaut (i.e. &auml;).
           See the HTML specification for the codes.
     </ul>
   </ul>
<li>Run configure and make again from the root of the distribution, 
    in order to regenerated the Makefiles.
<li>Now you can use <code>OUTPUT_LANGUAGE = your_language_name</code> 
    in the config file to generate output in your language.
<li>Send <code>translator_xx.h</code> to me so I can add it to doxygen.
    Send also your name and e-mail address to be included in the
    \c maintainers.txt list.
</ol>


<h3>Maintaining a language</h3>

New versions of doxygen may use new translated sentences.  In such
situation, the \c Translator class requires implementation of new
methods -- its interface changes.  Of course, the English
sentences need to be translated to the other languages.  At least,
new methods have to be implemented by the language-related
translator class; otherwise, doxygen wouldn't even compile.  Waiting
until all language maintainers have translated the new sentences and
sent the results would not be very practical. The following text
describes the usage of translator adapters to solve the problem.

<b>The role of Translator Adapters.</b> 
Whenever the \c Translator class interface changes in the new
release, the new class \c TranslatorAdapter_x_y_z is added to the \c
translator_adapter.h file (here x, y, and z are numbers that
correspond to the current official version of doxygen). All
translators that previously derived from the \c Translator class now
derive from this adapter class.

The \c TranslatorAdapter_x_y_z class implements the new, required
methods.  If the new method replaces some similar but obsolete
method(s) (e.g. if the number of arguments changed and/or the
functionality of the older method was changed or enriched), the \c
TranslatorAdapter_x_y_z class may use the obsolete method to get the
result which is as close as possible to the older result in the
target language.  If it is not possible, the result (the default
translation) is obtained using the English translator, which is (by
definition) always up-to-date.  

<b>For example,</b> when the new \c trFile() method with
parameters (to determine the capitalization of the first letter and
the singular/plural form) was introduced to replace the older method
\c trFiles() without arguments, the following code appeared in one
of the translator adapter classes:

\verbatim
    /*! This is the default implementation of the obsolete method
     * used in the documentation of a group before the list of
     * links to documented files.  This is possibly localized.
     */
    virtual QCString trFiles()
    { return "Files"; }

    /*! This is the localized implementation of newer equivalent
     * using the obsolete method trFiles().
     */
    virtual QCString trFile(bool first_capital, bool singular)
    {
      if (first_capital && !singular)
        return trFiles();  // possibly localized, obsolete method
      else
        return english.trFile(first_capital, singular);
    }
\endverbatim

The \c trFiles() is not present in the \c TranslatorEnglish class,
because it was removed as obsolete.  However, it was used until now
and its call was replaced by 

\verbatim
    trFile(true, false)
\endverbatim

in the doxygen source files.  Probably, many language translators
implemented the obsolete method, so it perfectly makes sense to use
the same language dependent result in those cases. The \c
TranslatorEnglish does not implement the old method.  It derives
from the abstract \c Translator class.  On the other hand, the old
translator for a different language does not implement the new \c
trFile() method.  Because of that it is derived from another base
class -- \c TranslatorAdapter_x_y_z. The \c TranslatorAdapter_x_y_z
class have to implement the new, required \c trFile() method.
However, the translator adapter would not be compiled if the \c
trFiles() method was not implemented. This is the reason for
implementing the old method in the translator adapter class (using
the same code, that was removed from the TranslatorEnglish).

The simplest way would be to pass the arguments to the English
translator and to return its result.  Instead, the adapter uses the
old \c trFiles() in one special case -- when the new
<code>trFile(true,&nbsp;false)</code> is called.  This is the
mostly used case at the time of introducing the new method -- see
above.  While this may look too complicated, the technique allows
the developers of the core sources to change the Translator
interface, while the users may not even notice the change.  Of
course, when the new \c trFile() is used with different arguments,
the English result is returned and it will be noticed by non English
users.  Here the maintainer of the language translator should
implement at least that one particular method.

<b>What says the base class of a language translator?</b>
If the language translator class inherits from any adapter class the
maintenance is needed.  In such case, the language translator is not
considered up-to-date.  On the other hand, if the language
translator derives directly from the abstract class \c Translator, the
language translator is up-to-date.

The translator adapter classes are chained so that the older
translator adapter class uses the one-step-newer translator adapter
as the base class.  The newer adapter does less \e adapting work
than the older one.  The oldest adapter class derives (indirectly)
from all of the adapter classes.  The name of the adapter class is
chosen so that its suffix is derived from the previous official
version of doxygen that did not need the adapter.  This way, one can
say approximately, when the language translator class was last
updated -- see details below.

The newest translator adapter derives from the abstract \c
TranslatorAdapterBase class that derives directly from the abstract
\c Translator class.  It adds only the private English-translator
member for easy implementation of the default translation inside the
adapter classes, and it also enforces implementation of one method
for noticing the user that the language translation is not up-to-date
(because of that some sentences in the generated files may appear in
English).

Once the oldest adapter class is not used by any of the language
translators, it can be removed from the doxygen project.  The
maintainers should try to reach the state with the minimal number of
translator adapter classes.

<b>To simplify the maintenance of the language translator classes</b>
for the supported languages, the \c translator.pl perl
script was developed (located in \c doxygen/doc directory). 
It extracts the important information about obsolete and
new methods from the source files for each of the languages.  
The information is stored in the <em>translator report</em> ASCII file
($translator_report_file_name). \htmlonly If you compiled this documentation
from sources and if you have also doxygen sources available the
link $translator_report_link should be valid.\endhtmlonly 

Looking at the base class of the language translator, the script
guesses also the status of the translator -- see the last column of
the table with languages above.  The \c translator.pl is called
automatically when the doxygen documentation is generated.  You can
also run the script manualy whenever you feel that it can help you.
Of course, you are not forced to use the results of the script.  You
can find the same information by looking at the adapter class and
its base classes.

<b>How should I update my language translator?</b> Firstly, you
should be the language maintainer, or you should let him/her know
about the changes.  The following text was written for the language
maintainers as the primary audience.

There are several approaches to be taken when updating your
language.  If you are not extremely busy, you should always chose
the most radical one.  When the update takes much more time than you
expected, you can always decide use some suitable translator adapter to
finish the changes later and still make your translator working.

<b>The most radical way of updating the language translator</b> is
to make your translator class derive directly 
from the abstract class \c Translator and provide translations for the
methods that are required to be implemented -- the compiler will
tell you if you forgot to implement some of them.  If you are in
doubt, have a look at the \c TranslatorEnglish class to recognize the
purpose of the implemented method.  Looking at the previously used
adapter class may help you sometimes, but it can also be misleading
because the adapter classes do implement also the obsolete methods
(see the previous \c trFiles() example).

In other words, the up-to-date language translators do not need the
\c TranslatorAdapter_x_y_z classes at all, and you do not need to
implement anything else than the methods required by the Translator
class (i.e. the pure virtual methods of the \c Translator -- they 
end with <code>=0;</code>).

If everything compiles fine, try to run \c translator.pl, and have a
look at the translator report (ASCII file) at the \c doxygen/doc
directory.  Even if your translator is marked as up-to-date, there
still may be some remarks related to your souce code.  Namely, the
obsolete methods--that are not used at all--may be listed in the
section for your language.  Simply, remove their code (and run the
\c translator.pl again).

<b>If you do not have time to finish all the updates</b> you should
still start with <em>the most radical approach</em> as described
above.  You can always change the base class to the translator
adapter class that implements all of the not-yet-implemented methods.

<b>If you prefer to update your translator gradually</b>, look
at the <em>translator report</em> generated by the \c translator.pl script
and choose one of the missing method that is implemented by the
translator adapter, that is used as your base class. When there is
not such a method in your translator adapter base class, you probably
can change the translator adapter base to the newer one.

Probably the easiest approach of the gradual update is to look at
the translator report to the part where the list of the implemented
translator adapters is shown. Then:
 - Look how many required methods each adapter implements and guess
   how many methods you are willing to update (to spend the time
   with).  
 - Choose the related oldest translator adapters to be removed (i.e.
   not used by your translator).
 - Change the base class of your translator class to the translator
   adapter that you want to use.
 - Implement the methods that were implemented by the older translator
   adapters.

Notice: Do not blindly implement all methods that are implemented by
your translator adapter base class.  The reason is that the adapter
classes implement also obsolete methods.  Another reason is that
some of the methods could become obsolete from some newer adapter
on.  Focus on the methods listed as \e required.

<b>The really obsolete language translators</b> may lead to too much
complicated adapters.  Because of that, doxygen developers may decide
to derive such translators from the \c TranslatorEnglish class, which 
is by definition always up-to-date.

When doing so, all the missing methods will be replaced by the
English translation.  This means that not-implemented methods will
always return the English result.  Such translators are marked using
word \c obsolete.  You should read it <b>really obsolete</b>. No
guess about the last update can be done.  

Often, it is possible to construct better result from the obsolete
methods.  Because of that, the translator adapter classes should be
used if possible.  On the other hand, implementation of adapters for
really obsolete translators brings too much maintenance and
run-time overhead.

*/

